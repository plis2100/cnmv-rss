# -*- coding: utf-8 -*-
import re
import os
import html
import argparse
import datetime as dt
import traceback
import hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from email.utils import format_datetime
import xml.etree.ElementTree as ET
from io import BytesIO
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup
import pdfplumber
from collections import Counter, defaultdict

BASE = "https://www.cnmv.es"

# ============================================================
# SALIDA: SIEMPRE en CWD\resultados (la carpeta desde la que ejecutas)
# ============================================================
def ensure_outdir(outdir_name="resultados") -> str:
    cwd = os.path.abspath(os.getcwd())
    outdir = os.path.join(cwd, outdir_name)
    os.makedirs(outdir, exist_ok=True)
    return outdir

def write_text_file(path: str, content: str, encoding="utf-8"):
    with open(path, "w", encoding=encoding, newline="\n") as f:
        f.write(content)
        f.flush()
        os.fsync(f.fileno())

def list_dir_files(path: str):
    try:
        return sorted(os.listdir(path))
    except Exception:
        return []

# ============================================================
# URLs CNMV: candidatos para evitar 404s
# ============================================================
def cnmv_candidates(url: str):
    if not url:
        return []

    u = url.strip()

    if u.startswith("/"):
        u = urljoin(BASE, u)
    elif not u.lower().startswith("http"):
        u = urljoin(BASE, "/" + u)

    if u.lower().startswith("http://www.cnmv.es/"):
        u = "https://www.cnmv.es/" + u[len("http://www.cnmv.es/"):]
    elif u.lower().startswith("http://cnmv.es/"):
        u = "https://www.cnmv.es/" + u[len("http://cnmv.es/"):]
    elif u.lower().startswith("https://cnmv.es/"):
        u = "https://www.cnmv.es/" + u[len("https://cnmv.es/"):]

    cands = [u]

    if "://www.cnmv.es/derechosvoto/" in u.lower():
        cands.append(re.sub(r"(?i)://www\.cnmv\.es/derechosvoto/",
                            "://www.cnmv.es/Portal/Consultas/derechosvoto/", u))
        cands.append(re.sub(r"(?i)://www\.cnmv\.es/derechosvoto/",
                            "://www.cnmv.es/portal/consultas/derechosvoto/", u))

    if "/portal/consultas/" in u.lower():
        cands.append(re.sub(r"(?i)/portal/consultas/", "/Portal/Consultas/", u))

    if "/Portal/Consultas/" in u:
        cands.append(u.replace("/Portal/Consultas/", "/portal/consultas/"))

    out, seen = [], set()
    for x in cands:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out

def fetch_html(session: requests.Session, url: str) -> str:
    last_err = None
    for u in cnmv_candidates(url):
        try:
            r = session.get(u, timeout=30, allow_redirects=True)
            r.raise_for_status()
            return r.text
        except Exception as e:
            last_err = e
    raise last_err

def fetch_bytes(session: requests.Session, url: str) -> bytes:
    last_err = None
    for u in cnmv_candidates(url):
        try:
            r = session.get(u, timeout=60, allow_redirects=True)
            r.raise_for_status()
            return r.content
        except Exception as e:
            last_err = e
    raise last_err

# ============================================================
# Utilidades fecha / numéricos
# ============================================================
DATE_RE = re.compile(r"\b(\d{2}/\d{2}/\d{4})\b")

def parse_date_es(s: str) -> dt.date:
    return dt.datetime.strptime(s, "%d/%m/%Y").date()

def fmt_date_es(d: dt.date) -> str:
    return d.strftime("%d/%m/%Y")

def parse_number(raw: str):
    if raw is None:
        return None
    s = str(raw).strip()
    s = re.sub(r"[^\d,.\-]", "", s)
    if not s:
        return None

    if "," in s and "." in s:
        if s.rfind(",") > s.rfind("."):
            s = s.replace(".", "").replace(",", ".")
        else:
            s = s.replace(",", "")
    else:
        if "," in s and "." not in s:
            parts = s.split(",")
            if len(parts) == 2 and 1 <= len(parts[1]) <= 3:
                s = s.replace(",", ".")
            else:
                s = s.replace(",", "")
        elif "." in s and "," not in s:
            parts = s.split(".")
            if not (len(parts) == 2 and 1 <= len(parts[1]) <= 2):
                s = s.replace(".", "")

    try:
        return float(s)
    except ValueError:
        return None

def fmt_int_if_whole(x):
    if x is None:
        return ""
    try:
        fx = float(x)
        if fx.is_integer():
            return str(int(fx))
        return str(fx)
    except Exception:
        return str(x)

def find_date_in_text(text: str) -> str:
    if not text:
        return ""
    m = DATE_RE.search(text)
    return m.group(1) if m else ""

# ============================================================
# BusquedaUltimosDias (vista por fecha)
# ============================================================
def build_busqueda_url(idPerfil=2, tipo=1, lang="es"):
    return f"{BASE}/portal/consultas/busquedaultimosdias?idPerfil={idPerfil}&tipo={tipo}&lang={lang}"

def extract_start_date_from_busqueda(soup: BeautifulSoup):
    text = soup.get_text(" ", strip=True)
    m = re.search(r"Incorporaci[oó]n\s+desde\s+el\s+d[ií]a\s+(\d{2}/\d{2}/\d{4})", text, re.I)
    return parse_date_es(m.group(1)) if m else None

def extract_psac_issuers_from_busqueda_view_by_date(soup: BeautifulSoup):
    items = []
    for li_date in soup.find_all("li"):
        tdate = " ".join(li_date.stripped_strings)
        m = DATE_RE.search(tdate or "")
        if not m:
            continue
        date_str = m.group(1)

        ul_inside = li_date.find("ul")
        if not ul_inside:
            continue

        target_li = None
        for subli in ul_inside.find_all("li", recursive=False):
            txt = " ".join(subli.stripped_strings)
            if ("Participaciones significativas" in txt) and ("Autocartera" in txt):
                target_li = subli
                break
        if not target_li:
            continue

        ul_emiters = target_li.find("ul")
        if not ul_emiters:
            continue

        for a in ul_emiters.find_all("a", href=True):
            href = cnmv_candidates(a["href"])[0]
            if "ps_ac_ini" not in href.lower():
                continue
            items.append({"fecha": date_str, "emisor": a.get_text(" ", strip=True), "ps_ac_ini_url": href})

    seen, out = set(), []
    for it in items:
        k = (it["fecha"], it["ps_ac_ini_url"])
        if k in seen:
            continue
        seen.add(k)
        out.append(it)
    return out

def extract_marked_dates_from_busqueda(soup: BeautifulSoup):
    """
    Devuelve las fechas 'cabecera' del listado (los días marcados) en orden DESC.
    """
    dates = set()
    for li_date in soup.find_all("li"):
        t = " ".join(li_date.stripped_strings)
        m = DATE_RE.search(t or "")
        if not m:
            continue
        ul_inside = li_date.find("ul")
        if not ul_inside:
            continue
        dates.add(m.group(1))

    return sorted(dates, key=lambda s: parse_date_es(s), reverse=True)

# ============================================================
# Landing ps_ac_ini -> links PS y AC
# ============================================================
def extract_ps_ac_links_from_psac_ini(soup: BeautifulSoup, base_url: str):
    links = {"ps_url": None, "ac_url": None}
    for a in soup.find_all("a", href=True):
        href = cnmv_candidates(urljoin(base_url, a["href"]))[0]
        hl = href.lower()
        if "notificaciones-participaciones" in hl:
            links["ps_url"] = href
        elif re.search(r"/autocartera(\.aspx)?\b", hl):
            links["ac_url"] = href
    return links

def find_other_notifications_url(soup: BeautifulSoup, base_url: str) -> str:
    """Devuelve el enlace real de ``OTRAS NOTIFICACIONES (1)``."""
    for a in soup.find_all("a", href=True):
        label = " ".join(a.stripped_strings).casefold()
        href = cnmv_candidates(urljoin(base_url, a["href"]))[0]
        if ("otras notificaciones" in label or
                "personasotrasnotificaciones" in href.casefold()):
            return href
    return ""

def extract_other_holder_links(soup: BeautifulSoup, base_url: str):
    """Extrae titular + histórico desde la página OTRAS NOTIFICACIONES."""
    holders = []
    for table in soup.find_all("table"):
        caption = " ".join(table.caption.stripped_strings).casefold() if table.caption else ""
        if "otras notificaciones" not in caption:
            continue
        for tr in table.find_all("tr"):
            cells = tr.find_all(["td", "th"], recursive=False)
            if not cells or not tr.find("td"):
                continue
            name = cells[0].get_text(" ", strip=True)
            link = next((a for a in tr.find_all("a", href=True)
                         if "notificacionesanteriores" in a["href"].casefold()), None)
            if name and link:
                holders.append((name, cnmv_candidates(urljoin(base_url, link["href"]))[0]))
    return holders

def collect_other_notifications(session: requests.Session, other_url: str):
    """Lee los históricos de todos los titulares del apartado de respaldo."""
    page = BeautifulSoup(fetch_html(session, other_url), "html.parser")
    holders = extract_other_holder_links(page, other_url)

    def read_one(holder_name, history_url):
        try:
            # Una sesión independiente por tarea evita compartir estado mutable
            # entre hilos y reduce mucho el tiempo cuando hay muchos titulares.
            local_session = requests.Session()
            local_session.headers.update(session.headers)
            history_soup = BeautifulSoup(fetch_html(local_session, history_url), "html.parser")
            holder_rows = extract_holder_history_rows(history_soup, history_url, holder_name)
            for row in holder_rows:
                row["historico_url"] = history_url
                row["section"] = "otras_notificaciones"
                row["from_other_notifications"] = True
            return holder_rows
        except Exception:
            return []

    rows = []
    with ThreadPoolExecutor(max_workers=min(6, max(1, len(holders)))) as pool:
        futures = [pool.submit(read_one, name, url) for name, url in holders]
        for future in as_completed(futures):
            rows.extend(future.result())
    return rows

# ============================================================
# PS (HTML): extraer tabla
# ============================================================
def pick_best_header_row(table):
    candidates = []
    for tr in table.find_all("tr"):
        ths = tr.find_all("th")
        if not ths:
            continue
        texts = [th.get_text(" ", strip=True) for th in ths]
        joined = " | ".join(t.lower() for t in texts)
        score = 0
        for kw in ["denomin", "(a+b)", "a+b", "directo", "indirecto", "registro", "entrada", "cnmv", "total", "(b)", "%"]:
            if kw in joined:
                score += 2
        non_empty = sum(1 for t in texts if t.strip())
        score += non_empty
        if non_empty <= 2:
            score -= 2
        candidates.append((score, tr, texts))
    if not candidates:
        return None, []
    candidates.sort(key=lambda x: x[0], reverse=True)
    best = candidates[0]
    return best[1], best[2]

def row_cells_including_th(tr):
    tds = tr.find_all("td")
    ths = tr.find_all("th")
    if not tds and ths and not any((th.get("scope") or "").lower() == "row" for th in ths):
        return []
    cells = tr.find_all(["th", "td"])
    return [c.get_text(" ", strip=True) for c in cells]

def normalize_holder_name(name: str) -> str:
    """Normaliza nombres para comparar el mismo titular entre tablas/históricos."""
    s = html.unescape(name or "").casefold().strip()
    s = re.sub(r"\([^)]*\)", " ", s)
    s = re.sub(r"[^a-záéíóúüñ0-9]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def _ps_table_section(table) -> str:
    """Intenta identificar si la tabla pertenece a participaciones vivas u otras notificaciones."""
    node = table
    for _ in range(12):
        node = node.find_previous()
        if node is None:
            break
        if getattr(node, "name", None) in ("h1", "h2", "h3", "h4", "h5", "legend", "strong", "b", "div", "p"):
            txt = " ".join(node.stripped_strings).strip()
            low = txt.casefold()
            if "otras notificaciones" in low or "otras participaciones" in low:
                return "otras_notificaciones"
            if "participaciones significativas" in low or "derechos de voto" in low:
                return "participaciones_vivas"
    return ""


def _extract_ps_rows_from_one_table(table, base_url: str):
    header_tr, headers = pick_best_header_row(table)
    if header_tr is None or not headers:
        return []

    headers_l = [re.sub(r"\s+", " ", h.casefold()).strip() for h in headers]
    joined_headers = " | ".join(headers_l)
    # Evita interpretar como participaciones las tablas de navegación/layout.
    if not any(k in joined_headers for k in ("denomin", "titular", "accionista", "notificante")):
        return []
    if not any(k in joined_headers for k in ("a+b", "total", "%")):
        return []

    def find_idx(groups):
        for group in groups:
            for i, h in enumerate(headers_l):
                if any(kw in h for kw in group):
                    return i
        return None

    idx_nombre = find_idx([
        ["denominación", "denominacion"],
        ["titular", "accionista", "notificante", "declarante", "persona", "nombre"],
    ])
    if idx_nombre is None:
        idx_nombre = 0

    idx_total_ab = find_idx([
        ["(a+b)", "a+b", "total (a+b)", "total a+b"],
        ["derechos de voto total", "% total", "total %"],
    ])
    idx_fecha = find_idx([
        ["f. registro entrada", "f.registro entrada", "registro entrada cnmv", "f. registro", "f.registro"],
        ["fecha"],
    ])

    section = _ps_table_section(table)
    out = []
    reached_header = False
    for tr in table.find_all("tr"):
        if tr == header_tr:
            reached_header = True
            continue
        if not reached_header:
            continue
        cells = row_cells_including_th(tr)
        if not cells:
            continue

        nombre = cells[idx_nombre] if idx_nombre < len(cells) else ""
        total_ab = cells[idx_total_ab] if idx_total_ab is not None and idx_total_ab < len(cells) else ""
        fecha = ""
        if idx_fecha is not None and idx_fecha < len(cells):
            fecha = find_date_in_text(cells[idx_fecha]) or cells[idx_fecha].strip()
        if not fecha:
            fecha = next((find_date_in_text(c) for c in cells if find_date_in_text(c)), "")

        detalle_url = ""
        historico_url = ""
        for a in tr.find_all("a", href=True):
            href = cnmv_candidates(urljoin(base_url, a["href"]))[0]
            label = " ".join(a.stripped_strings).casefold()
            href_l = href.casefold()
            if ("anterior" in label or "históric" in label or "historic" in label or
                    "notificaciones-anteriores" in href_l or "notificacionesanteriores" in href_l or "historico" in href_l):
                historico_url = href
            elif ("ver" in label or "detalle" in label or "notificacion" in href_l):
                if not detalle_url:
                    detalle_url = href

        if not (nombre and (fecha or total_ab or detalle_url or historico_url)):
            continue
        out.append({
            "nombre": nombre,
            "nombre_key": normalize_holder_name(nombre),
            "total_ab": total_ab,
            "fecha": fecha,
            "detalle_url": detalle_url,
            "historico_url": historico_url,
            "section": section,
            "prev_total_pct": None,
            "prev_date": None,
            "prev_source": None,
            "history_debug": "",
            "detail_pdf_url": None,
            "detail_pdf_text": None,
            "detail_pdf_text_truncated": False,
            "resulting_total_pct": None,
        })
    return out


def extract_ps_rows_from_html(ps_soup: BeautifulSoup, base_url: str):
    """
    Lee TODAS las tablas de participaciones de la página, incluida la tabla
    'OTRAS NOTIFICACIONES (1)'. La versión anterior solo utilizaba find('table').
    """
    rows = []
    for table in ps_soup.find_all("table"):
        rows.extend(_extract_ps_rows_from_one_table(table, base_url))

    unique, seen = [], set()
    for row in rows:
        key = (row.get("nombre_key"), row.get("fecha"), row.get("total_ab"),
               row.get("detalle_url"), row.get("historico_url"))
        if key in seen:
            continue
        seen.add(key)
        unique.append(row)

    unique.sort(
        key=lambda x: parse_date_es(x["fecha"]) if x.get("fecha") and DATE_RE.fullmatch(x["fecha"]) else dt.date.min,
        reverse=True,
    )
    return unique


def extract_holder_history_rows(hist_soup: BeautifulSoup, base_url: str, holder_name: str):
    """Extrae el histórico individual usando SIEMPRE la columna ``Total A+B``.

    La CNMV no usa siempre etiquetas ``<th>`` en esta ficha; en algunas versiones
    los encabezados son ``<td>``. Por eso se localiza la fila de cabecera por su
    contenido y no por el tipo de etiqueta HTML.
    """
    out = []
    holder_key = normalize_holder_name(holder_name)

    def norm(x):
        return re.sub(r"\s+", " ", (x or "").casefold()).strip()

    def is_total_ab_header(h):
        compact = re.sub(r"\s+", "", h)
        return (
            "a+b" in compact
            and ("total" in compact or "%" in compact)
        )

    def is_date_header(h):
        compact = re.sub(r"\s+", "", h)
        return (
            "registroentradacnmv" in compact
            or "f.registroentrada" in compact
            or compact == "fecha"
            or "fecharegistro" in compact
        )

    for table in hist_soup.find_all("table"):
        trs = table.find_all("tr")
        header_pos = None
        headers_l = []

        # La cabecera puede estar formada por TH o TD.
        for pos, tr in enumerate(trs):
            cells = tr.find_all(["th", "td"], recursive=False)
            if not cells:
                cells = tr.find_all(["th", "td"])
            texts = [norm(c.get_text(" ", strip=True)) for c in cells]
            if any(is_total_ab_header(h) for h in texts) and any(is_date_header(h) for h in texts):
                header_pos = pos
                headers_l = texts
                break

        if header_pos is None:
            continue

        idx_total_ab = next((i for i, h in enumerate(headers_l) if is_total_ab_header(h)), None)
        idx_fecha = next((i for i, h in enumerate(headers_l) if is_date_header(h)), None)
        if idx_total_ab is None or idx_fecha is None:
            continue

        for order, tr in enumerate(trs[header_pos + 1:]):
            cells_nodes = tr.find_all(["th", "td"], recursive=False)
            if not cells_nodes:
                cells_nodes = tr.find_all(["th", "td"])
            cells = [c.get_text(" ", strip=True) for c in cells_nodes]
            if max(idx_total_ab, idx_fecha) >= len(cells):
                continue

            total_ab = cells[idx_total_ab].strip()
            fecha = find_date_in_text(cells[idx_fecha]) or cells[idx_fecha].strip()
            if not total_ab or not DATE_RE.fullmatch(fecha):
                continue

            detalle_url = ""
            for a in tr.find_all("a", href=True):
                detalle_url = cnmv_candidates(urljoin(base_url, a["href"]))[0]
                break

            out.append({
                "nombre": holder_name,
                "nombre_key": holder_key,
                "total_ab": total_ab,
                "fecha": fecha,
                "detalle_url": detalle_url,
                "historico_url": "",
                "section": "historico_titular",
                "history_order": order,
            })

    # Evita duplicados, conservando el orden real mostrado por la CNMV.
    unique = []
    seen = set()
    for row in out:
        key = (row["fecha"], row["total_ab"], row.get("detalle_url", ""))
        if key in seen:
            continue
        seen.add(key)
        unique.append(row)
    return unique


def find_history_url_in_soup(soup: BeautifulSoup, base_url: str, holder_name: str = ""):
    """Localiza de forma robusta el enlace CNMV de notificaciones anteriores.

    Algunas páginas lo colocan en la misma fila del titular, otras en una fila
    auxiliar o dentro de la ficha de detalle. Se prioriza el enlace asociado al
    nombre del titular y, después, cualquier URL ``notificacionesanteriores``.
    """
    holder_key = normalize_holder_name(holder_name)
    candidates = []

    for a in soup.find_all("a", href=True):
        href = cnmv_candidates(urljoin(base_url, a["href"]))[0]
        label = " ".join(a.stripped_strings).casefold()
        href_l = href.casefold()
        is_history = (
            "notificacionesanteriores" in href_l
            or "notificaciones-anteriores" in href_l
            or "histórico" in label
            or "historico" in label
            or "notificaciones anteriores" in label
        )
        if not is_history:
            continue

        context_parts = []
        tr = a.find_parent("tr")
        if tr is not None:
            context_parts.append(" ".join(tr.stripped_strings))
            prev = tr.find_previous_sibling("tr")
            if prev is not None:
                context_parts.append(" ".join(prev.stripped_strings))
        parent = a.parent
        if parent is not None:
            context_parts.append(" ".join(parent.stripped_strings))
        context_key = normalize_holder_name(" ".join(context_parts))
        score = 0
        if holder_key and holder_key in context_key:
            score += 100
        if "notificacionesanteriores" in href_l:
            score += 20
        if "notificaciones anteriores" in label:
            score += 10
        candidates.append((score, href))

    if not candidates:
        return ""

    candidates.sort(key=lambda x: x[0], reverse=True)

    # MUY IMPORTANTE: si estamos buscando el histórico de un titular concreto
    # dentro de una página con varios accionistas, no se puede devolver un enlace
    # genérico perteneciente a otra fila. Solo se acepta un enlace cuyo contexto
    # contenga expresamente el mismo titular.
    if holder_key:
        holder_candidates = [item for item in candidates if item[0] >= 100]
        if not holder_candidates:
            return ""
        return holder_candidates[0][1]

    return candidates[0][1]


def attach_missing_history_urls(ps_soup: BeautifulSoup, base_url: str, rows):
    """Completa historico_url cuando la CNMV deja el enlace fuera del <tr>."""
    for row in rows:
        if not row.get("historico_url"):
            row["historico_url"] = find_history_url_in_soup(
                ps_soup, base_url, row.get("nombre", "")
            )
    return rows


def history_page_matches_holder(soup: BeautifulSoup, holder_name: str) -> bool:
    """Comprueba que una ficha histórica pertenece realmente al titular pedido.

    Evita reutilizar por error el histórico de otro accionista cuando la página
    principal contiene varios enlaces de "Notificaciones anteriores".
    """
    holder_key = normalize_holder_name(holder_name)
    if not holder_key:
        return False

    # Los títulos y cabeceras contienen normalmente el nombre del titular.
    pieces = []
    if soup.title:
        pieces.append(soup.title.get_text(" ", strip=True))
    for tag in soup.find_all(["h1", "h2", "h3", "h4", "caption", "legend", "strong"], limit=40):
        pieces.append(tag.get_text(" ", strip=True))
    page_key = normalize_holder_name(" ".join(pieces))
    if holder_key in page_key:
        return True

    # Respaldo limitado a la parte inicial visible, evitando asociar nombres que
    # aparezcan accidentalmente muy abajo en tablas de otros titulares.
    initial_text = " ".join(list(soup.stripped_strings)[:120])
    return holder_key in normalize_holder_name(initial_text)


def collect_ps_history_for_row(session: requests.Session, row: dict):
    """Lee la ficha de notificaciones anteriores del titular.

    Estrategia:
    1. usa ``historico_url`` capturada en la tabla principal;
    2. si falta o falla, abre la ficha de detalle y busca allí el enlace;
    3. si la propia ficha contiene la tabla histórica, la procesa directamente.
    """
    urls_to_try = []
    if row.get("historico_url"):
        urls_to_try.append(row["historico_url"])

    detail_url = row.get("detalle_url") or ""
    if detail_url:
        try:
            det_html = fetch_html(session, detail_url)
            det_soup = BeautifulSoup(det_html, "html.parser")

            # Algunas fichas ya contienen el histórico completo, pero solo se
            # acepta cuando la propia ficha identifica al mismo titular.
            if history_page_matches_holder(det_soup, row.get("nombre", "")):
                direct_rows = extract_holder_history_rows(
                    det_soup, detail_url, row.get("nombre", "")
                )
                if direct_rows:
                    return direct_rows

            found = find_history_url_in_soup(
                det_soup, detail_url, row.get("nombre", "")
            )
            if found and found not in urls_to_try:
                urls_to_try.append(found)
        except Exception:
            pass

    for history_url in urls_to_try:
        try:
            hist_html = fetch_html(session, history_url)
            hist_soup = BeautifulSoup(hist_html, "html.parser")

            # Si la ficha no menciona al titular, el enlace pertenece a otra fila
            # y se descarta por completo. Este era el origen de valores erróneos
            # como 30,236 atribuidos a BLACKROCK INC.
            if not history_page_matches_holder(hist_soup, row.get("nombre", "")):
                continue

            rows = extract_holder_history_rows(
                hist_soup, history_url, row.get("nombre", "")
            )
            if rows:
                return rows
            rows = extract_ps_rows_from_html(hist_soup, history_url)
            if rows:
                return rows
        except Exception:
            continue
    return []


def is_plausible_total_ab(value: str) -> bool:
    """Valida que Total A+B sea un porcentaje comprendido entre 0 y 100."""
    number = parse_number(value)
    return number is not None and 0 <= number <= 100


def select_previous_strict_date(current_row: dict, candidate_rows):
    """Devuelve la notificación más reciente con fecha ESTRICTAMENTE anterior.

    Si existen varias comunicaciones en la misma fecha que la actual, se ignoran
    todas. El dato devuelto siempre procede de la columna HTML ``Total A+B``.
    """
    try:
        current_date = parse_date_es((current_row.get("fecha") or "").strip())
    except Exception:
        return None

    holder_key = current_row.get("nombre_key") or normalize_holder_name(
        current_row.get("nombre", "")
    )
    valid = []
    for order, old in enumerate(candidate_rows or []):
        old_key = old.get("nombre_key") or normalize_holder_name(old.get("nombre", ""))
        if old_key != holder_key:
            continue
        total_ab = (old.get("total_ab") or "").strip()
        if not total_ab or not is_plausible_total_ab(total_ab):
            continue
        try:
            old_date = parse_date_es((old.get("fecha") or "").strip())
        except Exception:
            continue
        # Regla solicitada: saltar TODAS las filas de la misma fecha.
        if old_date >= current_date:
            continue
        valid.append((old_date, -order, old))

    if not valid:
        return None
    # Fecha anterior más cercana. Si hay varias ese día, conserva la primera
    # que aparece en el histórico de la CNMV.
    return max(valid, key=lambda item: (item[0], item[1]))[2]


def collect_first_pdf_link(soup: BeautifulSoup, base_url: str):
    for a in soup.find_all("a", href=True):
        href = urljoin(base_url, a["href"])
        if "/webservices/verdocumento/ver?e=" in href:
            return urljoin(BASE, href)
    return None

# ============================================================
# Autocartera (HTML): tabla como la foto
# ============================================================
def extract_autocartera_rows_from_html(ac_soup: BeautifulSoup, base_url: str):
    """
    Lee la tabla:
    % Directo | % Indirecto | % Total | F.Registro Entrada CNMV | Histórico de notificaciones
    """
    tables = ac_soup.find_all("table")
    if not tables:
        return []

    target_table = None
    for t in tables:
        headers = [th.get_text(" ", strip=True).lower() for th in t.find_all("th")]
        joined = " ".join(headers)
        if ("% directo" in joined) and ("% indirecto" in joined) and ("% total" in joined) and ("registro" in joined):
            target_table = t
            break
    if not target_table:
        target_table = tables[0]

    header_tr = target_table.find("tr")
    header_cells = [c.get_text(" ", strip=True).lower() for c in header_tr.find_all(["th", "td"])] if header_tr else []

    def col_idx(*keywords):
        for i, h in enumerate(header_cells):
            if all(k in h for k in keywords):
                return i
        for i, h in enumerate(header_cells):
            if any(k in h for k in keywords):
                return i
        return None

    idx_dir = col_idx("%", "directo")
    idx_ind = col_idx("%", "indirecto")
    idx_tot = col_idx("%", "total")
    idx_fecha = col_idx("registro")   # F.Registro Entrada CNMV
    idx_hist = col_idx("hist")        # Histórico

    rows = []
    trs = target_table.find_all("tr")
    for tr in trs[1:]:
        tds = tr.find_all(["td", "th"])
        if not tds:
            continue
        texts = [td.get_text(" ", strip=True) for td in tds]

        fecha = ""
        if idx_fecha is not None and idx_fecha < len(texts):
            fecha = find_date_in_text(texts[idx_fecha]) or texts[idx_fecha]
        if not fecha:
            for c in texts:
                f = find_date_in_text(c)
                if f:
                    fecha = f
                    break

        historico_url = ""
        if idx_hist is not None and idx_hist < len(tds):
            a_hist = tds[idx_hist].find("a", href=True)
            if a_hist:
                historico_url = urljoin(base_url, a_hist["href"])

        def get_val(i):
            return texts[i] if (i is not None and i < len(texts)) else ""

        rows.append({
            "pct_directo": get_val(idx_dir),
            "pct_indirecto": get_val(idx_ind),
            "pct_total": get_val(idx_tot),
            "fecha_registro": fecha,
            "historico_url": historico_url,
        })

    def key_fecha(r):
        try:
            return dt.datetime.strptime((r.get("fecha_registro") or "").strip(), "%d/%m/%Y")
        except Exception:
            return dt.datetime.min

    rows.sort(key=key_fecha, reverse=True)
    return rows

# ============================================================
# PDF utils: extraer texto completo (con límites)
# ============================================================
def extract_pdf_text(pdf_bytes: bytes, max_pages=None, max_chars=60000):
    parts = []
    with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
        pages = pdf.pages if max_pages is None else pdf.pages[:max_pages]
        for page in pages:
            try:
                t = page.extract_text() or ""
            except Exception:
                t = ""
            if t:
                parts.append(t)
    full = "\n\n".join(parts).strip()
    if not full:
        return "", False
    if max_chars is not None and len(full) > max_chars:
        return full[:max_chars], True
    return full, False

# ============================================================
# PDF parsing: AC (opcional, ya no manda)
# ============================================================
PDF_REG_RE = re.compile(r"Registro\s+de\s+entrada\s*(?:N[ºo]:)?\s*([0-9]+)\s+(?:Fecha\s*:)?\s*(\d{2}/\d{2}/\d{4})", re.I)
ISIN_RE = re.compile(r"\b([A-Z]{2}[A-Z0-9]{10})\b")

def extract_text_first_pages(pdf: pdfplumber.PDF, max_pages=3) -> str:
    parts = []
    for page in pdf.pages[:max_pages]:
        try:
            t = page.extract_text() or ""
        except Exception:
            t = ""
        if t.strip():
            parts.append(t)
    return "\n".join(parts)

def extract_ac_pdf(pdf_bytes: bytes):
    with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
        text = extract_text_first_pages(pdf, 3)

    reg, fecha = "", ""
    m = PDF_REG_RE.search(text)
    if m:
        reg, fecha = m.group(1), m.group(2)

    m_isin = ISIN_RE.search(text)
    isin = m_isin.group(1) if m_isin else ""

    def find_pct_near_keywords(t: str):
        kws = ["autocartera", "acciones propias", "accionespropias"]
        tl = t.lower()
        best_val = None
        best_dist = None

        for m in re.finditer(r"(\d{1,3}(?:[\.,]\d{3})*(?:[\.,]\d+)?)\s*%", t):
            raw = m.group(1)
            val = parse_number(raw)
            if val is None or not (0 <= val <= 100):
                continue
            pos = m.start()
            dmin = None
            for kw in kws:
                kpos = tl.find(kw)
                if kpos >= 0:
                    d = abs(pos - kpos)
                    dmin = d if dmin is None else min(dmin, d)
            if dmin is None:
                dmin = 10**9

            if best_val is None or dmin < best_dist:
                best_val = val
                best_dist = dmin
        return best_val

    pct = find_pct_near_keywords(text)

    acciones = None
    acc_patterns = [
        r"(?:n[ºo]\s*)?de\s*acciones\s*propias[^0-9]{0,80}(\d[\d\.,]*)",
        r"acciones\s*propias[^0-9]{0,80}(\d[\d\.,]*)",
        r"acciones\s*en\s*autocartera[^0-9]{0,80}(\d[\d\.,]*)",
        r"n[úu]mero\s*de\s*acciones[^0-9]{0,80}(\d[\d\.,]*)",
    ]
    for pat in acc_patterns:
        m_acc = re.search(pat, text, re.I | re.S)
        if m_acc:
            candidate = parse_number(m_acc.group(1))
            if candidate is not None:
                acciones = candidate
                break

    try:
        if reg and acciones is not None and str(int(float(acciones))) == str(int(reg)):
            acciones = None
    except Exception:
        pass

    return {
        "registro_entrada": reg,
        "fecha_entrada": fecha,
        "isin": isin,
        "acciones_propias": acciones,
        "porc_autocartera": pct,
        "precio": None,
    }

# ============================================================
# PDF parsing: Detalle PS (para sacar "anterior")
# ============================================================
PCT_ES_RE = re.compile(r"\b(\d{1,3}(?:\.\d{3})*,\d{3})\b")  # ej: 3,163 o 57.094,013
NA_RE = re.compile(r"\bN\.?A\.?\b", re.I)

def _find_pct_near_anchor(text: str, anchors, window=600):
    tl = text.lower()
    for a in anchors:
        idx = tl.find(a.lower())
        if idx >= 0:
            chunk = text[idx: idx + window]
            if NA_RE.search(chunk):
                pass
            m = PCT_ES_RE.search(chunk)
            if m:
                return m.group(1)
    return None

def extract_ps_prev_from_detail_pdf(pdf_bytes: bytes):
    with pdfplumber.open(BytesIO(pdf_bytes)) as pdf:
        text = extract_text_first_pages(pdf, 3)

    resulting = _find_pct_near_anchor(
        text,
        anchors=[
            "Situación resultante",
            "Resulting position",
            "Total % (7.A + 7.B)",
            "Total % (7A + 7B)",
            "Total of both in %"
        ],
        window=900
    )

    previous = _find_pct_near_anchor(
        text,
        anchors=[
            "Posición de la notificación previa",
            "Position of previous notification",
            "previa (si aplica)",
            "if applicable"
        ],
        window=900
    )

    return {
        "resulting_total_pct": resulting,
        "previous_total_pct": previous,
    }

# ============================================================
# Enriquecer emisor
# ============================================================
def enrich_issuer(session: requests.Session, item, window_start: dt.date, window_end: dt.date,
                  latest_busqueda_date: str, pdf_text_max_chars: int = 60000):
    result = {
        "fecha_listado": item["fecha"],
        "emisor": item["emisor"],
        "ps_ac_ini_url": item["ps_ac_ini_url"],
        "ps_rows": [],
        "ac_rows": [],   # ✅ tabla HTML como la foto
        "ac_pdfs": [],   # opcional
        "other_notifications_url": "",
        "other_notifications_used": False,
        "error": "",
    }

    try:
        psac_html = fetch_html(session, item["ps_ac_ini_url"])
        psac_soup = BeautifulSoup(psac_html, "html.parser")
        links = extract_ps_ac_links_from_psac_ini(psac_soup, item["ps_ac_ini_url"])
    except Exception as e:
        result["error"] = f"ps_ac_ini error: {type(e).__name__}: {e}"
        return result

    # -------------------------
    # PS
    # -------------------------
    if links.get("ps_url"):
        try:
            ps_html = fetch_html(session, links["ps_url"])
            ps_soup = BeautifulSoup(ps_html, "html.parser")
            # «OTRAS NOTIFICACIONES» es otra página; guardamos su enlace como respaldo.
            result["other_notifications_url"] = find_other_notifications_url(
                ps_soup, links["ps_url"]
            )
            ps_rows = extract_ps_rows_from_html(ps_soup, links["ps_url"])
            ps_rows = attach_missing_history_urls(ps_soup, links["ps_url"], ps_rows)

            filtered = []
            for rrow in ps_rows:
                if rrow.get("fecha"):
                    try:
                        d = parse_date_es(rrow["fecha"])
                        if not (window_start <= d <= window_end):
                            continue
                    except Exception:
                        pass

                # ✅ Para la última fecha buscada: leer PDF detalle,
                # sacar "previa" y además meter texto completo del PDF.
                if latest_busqueda_date and rrow.get("fecha") == latest_busqueda_date and rrow.get("detalle_url"):
                    try:
                        det_html = fetch_html(session, rrow["detalle_url"])
                        det_soup = BeautifulSoup(det_html, "html.parser")
                        pdf_url = collect_first_pdf_link(det_soup, rrow["detalle_url"])
                        if pdf_url:
                            pdf_bytes = fetch_bytes(session, pdf_url)

                            info = extract_ps_prev_from_detail_pdf(pdf_bytes)
                            # El PDF se conserva solo como respaldo. El valor anterior que se
                            # mostrará debe salir de la columna HTML "Total A+B" del histórico.
                            rrow["pdf_previous_total_pct"] = info.get("previous_total_pct")
                            rrow["resulting_total_pct"] = info.get("resulting_total_pct")
                            rrow["detail_pdf_url"] = pdf_url

                            txt, truncated = extract_pdf_text(
                                pdf_bytes,
                                max_pages=None,
                                max_chars=pdf_text_max_chars
                            )
                            rrow["detail_pdf_text"] = txt
                            rrow["detail_pdf_text_truncated"] = truncated
                    except Exception as e:
                        result["error"] += (" | " if result["error"] else "") + f"PS detalle PDF error: {type(e).__name__}: {e}"

                # En la fecha buscada, añade la posición de la FECHA ANTERIOR.
                # Se ignoran todas las comunicaciones registradas el mismo día,
                # aunque tengan otro Total A+B.
                if latest_busqueda_date and rrow.get("fecha") == latest_busqueda_date:
                    history_rows = collect_ps_history_for_row(session, rrow)
                    rrow["history_debug"] = f"URL histórico: {rrow.get('historico_url') or 'NO ENCONTRADA'} · filas leídas: {len(history_rows)}"

                    # 1) Histórico individual del titular.
                    previous_row = select_previous_strict_date(rrow, history_rows)

                    # 2) Respaldo: todas las tablas de la página, incluida
                    #    "OTRAS NOTIFICACIONES". También exige fecha anterior.
                    if previous_row is None:
                        previous_row = select_previous_strict_date(rrow, ps_rows)

                    if previous_row is not None:
                        rrow["prev_date"] = previous_row.get("fecha")
                        rrow["prev_total_pct"] = previous_row.get("total_ab")
                        rrow["prev_source"] = "Total A+B de la fecha anterior"
                    else:
                        # Participación realmente nueva: no existe ninguna comunicación
                        # con fecha estrictamente anterior. En ese caso, la posición
                        # anterior se representa expresamente como 0.00%.
                        # No se usa el PDF como sustituto porque podría confundirse A, B
                        # o A+B.
                        rrow["prev_total_pct"] = "0.00%"
                        rrow["prev_date"] = ""
                        rrow["prev_source"] = "Participación nueva: sin fecha anterior"
                        rrow["is_new_participation"] = True

                filtered.append(rrow)

            result["ps_rows"] = filtered
        except Exception as e:
            result["error"] += (" | " if result["error"] else "") + f"PS error: {type(e).__name__}: {e}"

    # -------------------------
    # AC (HTML como la foto + PDF opcional)
    # -------------------------
    if links.get("ac_url"):
        try:
            ac_html = fetch_html(session, links["ac_url"])
            ac_soup = BeautifulSoup(ac_html, "html.parser")

            # ✅ 1) DATOS BUENOS: tabla HTML (como tu captura)
            result["ac_rows"] = extract_autocartera_rows_from_html(ac_soup, links["ac_url"])

            # ✅ 2) PDF opcional (filtrado anti-ruido)
            pdf_url = collect_first_pdf_link(ac_soup, links["ac_url"])
            if pdf_url:
                try:
                    pdf_bytes = fetch_bytes(session, pdf_url)
                    data = extract_ac_pdf(pdf_bytes)

                    # filtro anti-basura: si te sale 1 / 1.0, lo anulamos
                    if data.get("acciones_propias") in (1, 1.0):
                        data["acciones_propias"] = None
                    if data.get("porc_autocartera") in (1, 1.0):
                        data["porc_autocartera"] = None

                    result["ac_pdfs"].append({"pdf_url": pdf_url, **data})
                except Exception as e:
                    result["error"] += (" | " if result["error"] else "") + f"AC PDF parse error: {type(e).__name__}: {e}"
        except Exception as e:
            result["error"] += (" | " if result["error"] else "") + f"AC error: {type(e).__name__}: {e}"

    # Si las dos consultas principales no contienen ninguna fila de la fecha
    # que debe salir verde, continuar obligatoriamente en OTRAS NOTIFICACIONES.
    has_latest_ps = any(
        (row.get("fecha") or "").strip() == latest_busqueda_date
        for row in result.get("ps_rows", [])
    )
    has_latest_ac = any(
        (row.get("fecha_registro") or "").strip() == latest_busqueda_date
        for row in result.get("ac_rows", [])
    )
    if (latest_busqueda_date and not has_latest_ps and not has_latest_ac and
            result.get("other_notifications_url")):
        try:
            all_other_rows = collect_other_notifications(session, result["other_notifications_url"])
            latest_other_rows = [row for row in all_other_rows
                                 if (row.get("fecha") or "").strip() == latest_busqueda_date]
            for row in latest_other_rows:
                previous = select_previous_strict_date(row, all_other_rows)
                if previous is not None:
                    row["prev_date"] = previous.get("fecha")
                    row["prev_total_pct"] = previous.get("total_ab")
                    row["prev_source"] = "OTRAS NOTIFICACIONES: Total A+B anterior"
                else:
                    row["prev_total_pct"] = "0.00%"
                    row["prev_date"] = ""
                    row["prev_source"] = "OTRAS NOTIFICACIONES: participación nueva"
                    row["is_new_participation"] = True
            if latest_other_rows:
                result["ps_rows"].extend(latest_other_rows)
                result["other_notifications_used"] = True
        except Exception as e:
            result["error"] += (" | " if result["error"] else "") + (
                f"OTRAS NOTIFICACIONES error: {type(e).__name__}: {e}"
            )

    return result

# ============================================================
# HTML
# ============================================================
def render_html(window_start: dt.date, window_end: dt.date, results, fuente_url: str, keep_dates, latest_busqueda_date: str):
    esc = html.escape
    keep_set = set(keep_dates or [])

    def cls_for_date(date_str: str) -> str:
        """
        ROJO: si está en keep_dates
        VERDE: si es la última fecha buscada (sobrescribe)
        """
        if latest_busqueda_date and date_str == latest_busqueda_date:
            return " class='latestrow'"
        if date_str in keep_set:
            return " class='hotrow'"
        return ""

    # ✅ Para el DETALLE: quedarnos SOLO con la fecha más reciente por emisor
    latest_by_emisor = {}
    for r in results:
        em = (r.get("emisor") or "").strip()
        if not em:
            continue
        try:
            d = dt.datetime.strptime(r.get("fecha_listado", ""), "%d/%m/%Y").date()
        except Exception:
            d = dt.date.min

        if em not in latest_by_emisor or d > latest_by_emisor[em][0]:
            latest_by_emisor[em] = (d, r)

    detail_results = [v[1] for v in latest_by_emisor.values()]
    detail_results.sort(
        key=lambda x: (
            dt.datetime.strptime(x.get("fecha_listado", "01/01/1900"), "%d/%m/%Y"),
            (x.get("emisor") or "").lower()
        ),
        reverse=True
    )

    by_fecha = Counter(r["fecha_listado"] for r in results)

    css = """
    body{font-family:Arial,Helvetica,sans-serif;margin:24px;line-height:1.25}
    h1{font-size:20px;margin:0 0 8px 0}
    .meta{color:#555;margin-bottom:10px}
    .card{border-top:1px solid #ddd;padding:12px 0}
    .issuer{font-weight:bold;margin-top:4px}
    a{color:#b1002a;text-decoration:none}
    a:hover{text-decoration:underline}
    table{border-collapse:collapse;margin-top:8px;font-size:13px;width:100%}
    th,td{border:1px solid #ddd;padding:6px 8px}
    th{background:#f5f5f5;text-align:left}
    td.num{text-align:right}
    .small{font-size:12px;color:#666}
    .warn{color:#b1002a;font-size:12px}

    /* ROJO = datos en fechas pedidas (keep_dates) */
    .hotrow td{color:#d00000 !important;font-weight:700}
    .hotrow a{color:#d00000 !important;font-weight:700}

    /* VERDE = datos de la última fecha buscada (sobrescribe) */
    .latestrow td{color:#138a08 !important;font-weight:700}
    .latestrow a{color:#138a08 !important;font-weight:700}

    /* Bloques de texto PDF (detalle PS) */
    details.pdfbox{margin:8px 0 0 0}
    details.pdfbox summary{cursor:pointer;color:#333}
    pre.pdftxt{white-space:pre-wrap;word-wrap:break-word;background:#fafafa;border:1px solid #eee;padding:10px;border-radius:6px;max-height:420px;overflow:auto}
    .trunc{color:#b1002a;font-size:12px;margin-top:4px}

    /* fila auxiliar para "Anterior (PDF)" en gris */
    .prevrow td{color:#666 !important;font-style:italic}
    """

    out = [f"<!doctype html><html><head><meta charset='utf-8'><style>{css}</style></head><body>"]
    out.append("<h1>CNMV · PS (HTML) + Autocartera (HTML) · últimos días (según BusquedaUltimosDias)</h1>")

    latest_label = ""
    if latest_busqueda_date:
        latest_label = f" · Última fecha búsqueda: <span style='color:#138a08;font-weight:700'>{esc(latest_busqueda_date)}</span>"

    out.append(
        f"<div class='meta'>Fuente: <a href='{esc(fuente_url)}' target='_blank' rel='noopener'>BusquedaUltimosDias</a>"
        f" · Ventana: <b>{esc(fmt_date_es(window_start))}</b> → <b>{esc(fmt_date_es(window_end))}</b>"
        f"{latest_label}"
        f" · Emisores: <b>{len(results)}</b></div>"
    )

    out.append("<div class='small'><b>Emisores por fecha del listado</b></div>")
    for f, n in sorted(by_fecha.items(), key=lambda kv: dt.datetime.strptime(kv[0], "%d/%m/%Y"), reverse=True):
        row_style = ""
        if latest_busqueda_date and f == latest_busqueda_date:
            row_style = " style='color:#138a08;font-weight:700'"
        elif f in keep_set:
            row_style = " style='color:#d00000;font-weight:700'"
        out.append(f"<div class='small'{row_style}>{esc(f)}: <b>{n}</b></div>")

    # LISTADO DE EMPRESAS POR FECHA
    companies_by_date = defaultdict(list)
    seen_by_date = defaultdict(set)
    for r in results:
        f = (r.get("fecha_listado") or "").strip()
        name = (r.get("emisor") or "").strip()
        if not f or not name:
            continue
        key = re.sub(r"\s+", " ", name).lower()
        if key in seen_by_date[f]:
            continue
        seen_by_date[f].add(key)
        companies_by_date[f].append(name)

    out.append("<div style='margin-top:10px'><b>Listado de empresas por fecha</b></div>")
    for f in sorted(companies_by_date.keys(), key=lambda s: dt.datetime.strptime(s, "%d/%m/%Y"), reverse=True):
        h_style = ""
        if latest_busqueda_date and f == latest_busqueda_date:
            h_style = "color:#138a08;font-weight:700"
        elif f in keep_set:
            h_style = "color:#d00000;font-weight:700"
        out.append(f"<div class='small' style='margin-top:6px;{h_style}'><b>{esc(f)}</b> ({len(companies_by_date[f])})</div>")
        out.append("<ul style='margin-top:4px'>")
        for nm in sorted(companies_by_date[f], key=lambda s: s.lower()):
            out.append(f"<li class='small'>{esc(nm)}</li>")
        out.append("</ul>")

    # DETALLE POR EMISOR
    for r in detail_results:
        out.append("<div class='card'>")

        f_em = r.get("fecha_listado", "")
        if latest_busqueda_date and f_em == latest_busqueda_date:
            out.append(f"<div style='color:#138a08;font-weight:700'><b>{esc(f_em)}</b></div>")
        elif f_em in keep_set:
            out.append(f"<div style='color:#d00000;font-weight:700'><b>{esc(f_em)}</b></div>")
        else:
            out.append(f"<div><b>{esc(f_em)}</b></div>")

        out.append(f"<div class='issuer'>{esc(r['emisor'])}</div>")
        out.append(f"<div class='small'>Landing: <a href='{esc(r['ps_ac_ini_url'])}' target='_blank' rel='noopener'>ps_ac_ini</a></div>")
        if r.get("other_notifications_used"):
            out.append(
                "<div class='small' style='color:#138a08;font-weight:700'>"
                f"Resultado encontrado mediante <a href='{esc(r.get('other_notifications_url',''))}' "
                "target='_blank' rel='noopener'>OTRAS NOTIFICACIONES (1)</a></div>"
            )
        if r.get("error"):
            out.append(f"<div class='warn'>⚠ {esc(r['error'])}</div>")

        # =======================
        # PARTICIPACIONES (PS)
        # =======================
        out.append("<div style='margin-top:8px'><b>Participaciones significativas</b></div>")
        if r["ps_rows"]:
            out.append("<table>")
            out.append("<tr><th>#</th><th>Nombre</th><th class='num'>Total A+B</th><th>Fecha</th><th>Detalle</th></tr>")
            for i, it in enumerate(r["ps_rows"], 1):
                fecha_ps = (it.get("fecha") or "").strip()
                tr_cls = cls_for_date(fecha_ps)
                detail_url = it.get("detalle_url") or it.get("historico_url") or ""
                detalle = f"<a href='{esc(detail_url)}' target='_blank' rel='noopener'>Ver</a>" if detail_url else ""
                source_note = " <span class='small'>(Otras notificaciones)</span>" if it.get("from_other_notifications") else ""
                out.append(
                    f"<tr{tr_cls}>"
                    f"<td>{i}</td><td>{esc(it.get('nombre',''))}{source_note}</td>"
                    f"<td class='num'><b>{esc(it.get('total_ab',''))}</b></td>"
                    f"<td>{esc(fecha_ps)}</td><td>{detalle}</td>"
                    f"</tr>"
                )

                # Posición anterior: si no existe una fecha estrictamente anterior,
                # se muestra 0.00% como participación nueva.
                if latest_busqueda_date and fecha_ps == latest_busqueda_date and it.get("prev_total_pct") is not None:
                    previous_label = (
                        "↳ Participación nueva · Total A+B anterior"
                        if it.get("is_new_participation")
                        else "↳ Fecha anterior · Total A+B"
                    )
                    out.append(
                        "<tr class='prevrow'>"
                        f"<td></td>"
                        f"<td>{esc(previous_label)}</td>"
                        f"<td class='num'><b>{esc(str(it.get('prev_total_pct')))}</b></td>"
                        f"<td>{esc(it.get('prev_date') or '')}</td>"
                        f"<td></td>"
                        "</tr>"
                    )

                # Texto completo del PDF del detalle (solo en última fecha)
                if latest_busqueda_date and fecha_ps == latest_busqueda_date and it.get("detail_pdf_text"):
                    pdfurl = it.get("detail_pdf_url") or ""
                    out.append("<tr><td colspan='5'>")
                    out.append("<details class='pdfbox'>")
                    if pdfurl:
                        out.append(
                            f"<summary><b>Texto completo del PDF (detalle)</b> · "
                            f"<a href='{esc(pdfurl)}' target='_blank' rel='noopener'>PDF</a></summary>"
                        )
                    else:
                        out.append("<summary><b>Texto completo del PDF (detalle)</b></summary>")
                    out.append(f"<pre class='pdftxt'>{esc(it.get('detail_pdf_text',''))}</pre>")
                    if it.get("detail_pdf_text_truncated"):
                        out.append("<div class='trunc'>⚠ Texto recortado por tamaño (ajusta --pdf_text_max_chars si quieres más).</div>")
                    out.append("</details>")
                    out.append("</td></tr>")

            out.append("</table>")
        else:
            out.append("<div class='small'>— Sin filas PS.</div>")

        # =======================
        # AUTOCARTERA (HTML como la foto)
        # =======================
        out.append("<div style='margin-top:8px'><b>Notificaciones sobre acciones propias (Autocartera)</b></div>")
        if r.get("ac_rows"):
            out.append("<table>")
            out.append("<tr><th>#</th><th class='num'>% Directo</th><th class='num'>% Indirecto</th><th class='num'>% Total</th>"
                       "<th>F. Registro Entrada CNMV</th><th>Histórico</th></tr>")
            for i, it in enumerate(r["ac_rows"], 1):
                fecha_ac = (it.get("fecha_registro") or "").strip()
                tr_cls = cls_for_date(fecha_ac)

                hist = ""
                if it.get("historico_url"):
                    hist = f"<a href='{esc(it['historico_url'])}' target='_blank' rel='noopener'>Ver</a>"

                out.append(
                    f"<tr{tr_cls}>"
                    f"<td>{i}</td>"
                    f"<td class='num'>{esc(it.get('pct_directo',''))}</td>"
                    f"<td class='num'>{esc(it.get('pct_indirecto',''))}</td>"
                    f"<td class='num'><b>{esc(it.get('pct_total',''))}</b></td>"
                    f"<td>{esc(fecha_ac)}</td>"
                    f"<td>{hist}</td>"
                    f"</tr>"
                )
            out.append("</table>")
        else:
            out.append("<div class='small'>— Sin filas en Autocartera (HTML).</div>")

        out.append("</div>")

    out.append("</body></html>")
    return "\n".join(out)

# ============================================================
# RSS 2.0 PARA FEEDLY
# ============================================================
def render_rss(results, fuente_url: str):
    """Genera una RSS válida con GUID estable para evitar duplicados en Feedly."""
    rss = ET.Element("rss", {"version": "2.0"})
    channel = ET.SubElement(rss, "channel")
    ET.SubElement(channel, "title").text = "CNMV · Participaciones y autocartera"
    ET.SubElement(channel, "link").text = fuente_url
    ET.SubElement(channel, "description").text = (
        "Notificaciones de participaciones significativas, autocartera y "
        "otras notificaciones publicadas por la CNMV."
    )
    ET.SubElement(channel, "language").text = "es"
    ET.SubElement(channel, "lastBuildDate").text = format_datetime(
        dt.datetime.now(dt.timezone.utc)
    )

    entries = []
    for result in results:
        issuer = (result.get("emisor") or "").strip()

        for row in result.get("ps_rows", []):
            date_str = (row.get("fecha") or "").strip()
            holder = (row.get("nombre") or "").strip()
            total = (row.get("total_ab") or "").strip()
            link = (row.get("detalle_url") or row.get("historico_url") or
                    result.get("other_notifications_url") or result.get("ps_ac_ini_url") or fuente_url)
            source = "Otras notificaciones" if row.get("from_other_notifications") else "Participación significativa"
            title = f"{issuer}: {holder} · Total A+B {total}"
            description = (
                f"<b>Empresa:</b> {html.escape(issuer)}<br>"
                f"<b>Titular:</b> {html.escape(holder)}<br>"
                f"<b>Total A+B:</b> {html.escape(total)}<br>"
                f"<b>Fecha CNMV:</b> {html.escape(date_str)}<br>"
                f"<b>Origen:</b> {html.escape(source)}"
            )
            if row.get("prev_total_pct") is not None:
                description += (
                    f"<br><b>Total A+B anterior:</b> {html.escape(str(row.get('prev_total_pct')))}"
                    f"<br><b>Fecha anterior:</b> {html.escape(row.get('prev_date') or 'Sin fecha anterior')}"
                )
            stable_key = "|".join(("PS", issuer, holder, date_str, total, link))
            entries.append((date_str, title, description, link, stable_key))

        for row in result.get("ac_rows", []):
            date_str = (row.get("fecha_registro") or "").strip()
            total = (row.get("pct_total") or "").strip()
            link = row.get("historico_url") or result.get("ps_ac_ini_url") or fuente_url
            title = f"{issuer}: autocartera · {total}%"
            description = (
                f"<b>Empresa:</b> {html.escape(issuer)}<br>"
                f"<b>% directo:</b> {html.escape(row.get('pct_directo') or '')}<br>"
                f"<b>% indirecto:</b> {html.escape(row.get('pct_indirecto') or '')}<br>"
                f"<b>% total:</b> {html.escape(total)}<br>"
                f"<b>Fecha CNMV:</b> {html.escape(date_str)}"
            )
            stable_key = "|".join(("AC", issuer, date_str, total, link))
            entries.append((date_str, title, description, link, stable_key))

    def entry_date(entry):
        try:
            return parse_date_es(entry[0])
        except Exception:
            return dt.date.min

    for date_str, title, description, link, stable_key in sorted(
            entries, key=entry_date, reverse=True):
        item = ET.SubElement(channel, "item")
        ET.SubElement(item, "title").text = title
        ET.SubElement(item, "link").text = link
        ET.SubElement(item, "description").text = description
        guid = ET.SubElement(item, "guid", {"isPermaLink": "false"})
        guid.text = hashlib.sha256(stable_key.encode("utf-8")).hexdigest()
        try:
            published = dt.datetime.combine(
                parse_date_es(date_str), dt.time(12, 0), tzinfo=dt.timezone.utc
            )
            ET.SubElement(item, "pubDate").text = format_datetime(published)
        except Exception:
            pass

    ET.indent(rss, space="  ")
    return "<?xml version='1.0' encoding='UTF-8'?>\n" + ET.tostring(
        rss, encoding="unicode", short_empty_elements=True
    ) + "\n"

# ============================================================
# MAIN
# ============================================================
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--perfil", type=int, default=2)
    parser.add_argument("--keep_days", type=int, default=5, help="Número de días (fechas cabecera) a conservar")
    parser.add_argument("--pdf_text_max_chars", type=int, default=60000, help="Máximo de caracteres del texto PDF embebido en el HTML")
    args = parser.parse_args()

    outdir = ensure_outdir("resultados")
    errlog = os.path.join(outdir, "error.log")

    try:
        write_text_file(os.path.join(outdir, "BOOTSTRAP_OK.txt"),
                        f"Bootstrap OK\nCWD={os.getcwd()}\nOUTDIR={outdir}\nTIME={dt.datetime.now().isoformat()}\n")
    except Exception:
        pass

    try:
        fuente_url = build_busqueda_url(idPerfil=args.perfil, tipo=1, lang="es")

        session = requests.Session()
        session.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0 Safari/537.36"
            ),
            "Accept-Language": "es-ES,es;q=0.9,en;q=0.8",
        })

        print("DEBUG cwd:", os.getcwd())
        print("DEBUG outdir:", outdir)
        print("DEBUG URL:", fuente_url)

        html_src = fetch_html(session, fuente_url)
        soup = BeautifulSoup(html_src, "html.parser")
        txt = soup.get_text(" ", strip=True)

        # 1) Fechas marcadas y quedarnos con las N más recientes
        marked_dates = extract_marked_dates_from_busqueda(soup)
        keep_dates = marked_dates[: max(args.keep_days, 0)]
        keep_set = set(keep_dates)

        latest_busqueda_date = keep_dates[0] if keep_dates else ""

        print("DEBUG fechas marcadas encontradas:", len(marked_dates))
        print("DEBUG fechas que se conservan:", keep_dates)
        print("DEBUG última fecha búsqueda:", latest_busqueda_date)

        if keep_dates:
            window_end = parse_date_es(keep_dates[0])
            window_start = parse_date_es(keep_dates[-1])
        else:
            window_start = extract_start_date_from_busqueda(soup) or (dt.date.today() - dt.timedelta(days=5))
            all_dates = [parse_date_es(m.group(1)) for m in DATE_RE.finditer(txt)]
            window_end = max(all_dates) if all_dates else dt.date.today()

        # 2) Emisores filtrados por esas fechas pedidas
        issuers_all = extract_psac_issuers_from_busqueda_view_by_date(soup)
        issuers = [it for it in issuers_all if (it.get("fecha") in keep_set)]

        print("DEBUG emisores encontrados total:", len(issuers_all))
        print("DEBUG emisores tras filtrar por fechas pedidas:", len(issuers))

        # 3) Enriquecer + render
        results = [
            enrich_issuer(
                session,
                it,
                window_start,
                window_end,
                latest_busqueda_date,
                pdf_text_max_chars=args.pdf_text_max_chars
            )
            for it in issuers
        ]
        html_out = render_html(window_start, window_end, results, fuente_url, keep_dates, latest_busqueda_date)

        fname = f"cnmv_ps_ac_{window_start.strftime('%Y%m%d')}_{window_end.strftime('%Y%m%d')}.html"
        outpath = os.path.abspath(os.path.join(outdir, fname))
        print("DEBUG outpath final:", outpath)

        write_text_file(outpath, html_out)

        # GitHub y Feedly leerán siempre este archivo estable en la raíz.
        feed_path = os.path.abspath(os.path.join(os.getcwd(), "feed.xml"))
        write_text_file(feed_path, render_rss(results, fuente_url))

        print(f"✔ Generado HTML en: {outpath}")
        print(f"✔ Generada RSS en: {feed_path}")
        print("DEBUG archivos en resultados:", list_dir_files(outdir))

    except Exception:
        tb = traceback.format_exc()
        try:
            write_text_file(errlog, tb)
        except Exception:
            pass
        print("❌ Error: revisa", errlog)
        print(tb)

if __name__ == "__main__":
    main()
