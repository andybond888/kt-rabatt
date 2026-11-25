"""
Självgående molnskript (update_cloud_page.py) – körs automatiskt i GitHub Actions varje morgon
(och lokalt vid publicering) helt utan externa paket.
Hämtar aktuella reklamblad runt Huddinge/Söderort, jämför mot baselines.json och bygger mobilrabattlistan.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

ROOT_DIR = Path(__file__).resolve().parent
BASELINES_FILE = ROOT_DIR / "baselines.json"
PUBLIC_DIR = ROOT_DIR / "public"


def parse_sv_float(val: Any) -> float:
    if val is None:
        return 0.0
    if isinstance(val, (int, float)):
        return float(val)
    s = str(val).strip().replace("\u00a0", "").replace(" ", "").replace(",", ".")
    s = re.sub(r"[^0-9.\-]", "", s)
    try:
        return float(s) if s and s not in ("-", ".", "-.") else 0.0
    except ValueError:
        return 0.0


def compute_net_from_gross(gross: float, vat_rate: float) -> float:
    return gross / (1.0 + vat_rate / 100.0) if vat_rate > 0 else gross


def swedish_now() -> datetime:
    # Enkel svensk tid (CET/CEST) utan tredjepartsbibliotek
    utc_now = datetime.now(timezone.utc)
    # Sommartid sista söndagen i mars till sista söndagen i oktober (förenklat: apr-okt = +2, nov-feb = +1)
    offset_h = 2 if 4 <= utc_now.month <= 10 else 1
    return utc_now + timedelta(hours=offset_h)


def match_slug(text: str, rules: List[Dict[str, Any]]) -> Optional[str]:
    low = (text or "").lower()
    for rule in rules:
        for pat in rule["patterns"]:
            if re.search(pat, low, re.I):
                return str(rule["slug"])
    return None


def normalize_offer(
    store_name: str,
    offer: Dict[str, Any],
    food_vat_rate: float,
    non_food_keywords: List[str],
    rules: List[Dict[str, Any]],
    baselines: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    pricing = offer.get("pricing") or {}
    if pricing.get("currency") and pricing.get("currency") != "SEK":
        return None
    price_gross = float(pricing.get("price") or 0.0)
    if price_gross <= 0:
        return None

    heading = (offer.get("heading") or "").strip()
    desc = (offer.get("description") or "").strip()
    full_txt = f"{heading} {desc}".strip()
    low_txt = full_txt.lower()

    vat_r = 25.0 if any(k in low_txt for k in non_food_keywords) else food_vat_rate
    price_net = compute_net_from_gross(price_gross, vat_r)

    slug = match_slug(heading, rules)
    if slug is None and any(
        w in heading.lower()
        for w in ("läsk", "cola", "fanta", "sprite", "pepsi", "loka", "ramlösa", "mariestad", "norrland", "eriksberg")
    ):
        slug = match_slug(full_txt, rules)

    if slug and any(
        bad in low_txt
        for bad in (
            "chips",
            "godis",
            "choklad",
            "glass",
            "kex",
            "kaka",
            "hund",
            "katt",
            "smörgåspålägg",
            "skaldjursbricka",
            "porchetta",
            "kebab",
            "panerade",
            "ketchup",
        )
    ):
        slug = None
    if slug == "farsk_lax" and any(bad in low_txt for bad in ("rökt", "gravad", "fryst", "paj", "soppa")):
        slug = None
    if slug == "tomat" and any(bad in low_txt for bad in ("krossade", "passerade", "puré", "pure", "sås", "ketchup", "soltork", "på burk")):
        slug = None

    if not slug or slug not in baselines:
        return None

    b_info = baselines[slug]
    canon_unit = b_info["unit"]
    default_yield = float(b_info.get("yield_pct", 100.0))

    max_note = ""
    m_max = re.search(r"(max\s+\d+\s+[^.\n]{2,25})", desc, re.I)
    if m_max:
        max_note = m_max.group(1).strip()

    q_obj = offer.get("quantity") or {}
    pieces_from = float(((q_obj.get("pieces") or {}).get("from")) or 1.0)
    pieces_max = (q_obj.get("pieces") or {}).get("max")
    if not max_note and pieces_max:
        max_note = f"Max {pieces_max} köp"

    size_obj = q_obj.get("size") or {}
    sz_from = float(size_obj.get("from") or 1.0)
    sz_to = float(size_obj.get("to") or sz_from)
    sz_avg = (sz_from + sz_to) / 2.0

    si_obj = ((q_obj.get("unit") or {}).get("si")) or {}
    si_sym = str(si_obj.get("symbol") or "pcs").lower()
    si_fac = float(si_obj.get("factor") or 1.0)

    norm_qty = 1.0
    norm_unit = "st"
    unit_price_net = price_net

    m_cans = re.search(r"\b(\d{1,2})\s*(?:p|st)?\s*[/x×*]\s*(33|50)\s*cl\b|\b(\d{1,2})\s*-?\s*pack\b", full_txt, re.I)
    has_33_50 = bool(re.search(r"(?:^|[\s/×xX*(])(33|50)\s*cl\b", full_txt, re.I))
    m_jfr_any = re.search(
        r"j(?:fr|mf|ämför)[.\s-]*(?:pris)?\s*:?\s*(\d+(?:[.,:]\d+)?)\s*(?:kr|:-)?\s*/\s*(kg|l|st)\b",
        desc,
        re.I,
    )

    if (canon_unit == "st" and has_33_50) or (
        has_33_50 and any(w in low_txt for w in ("cola", "fanta", "sprite", "pepsi", "loka", "ramlösa", "läsk", "julmust", "öl"))
    ):
        can_vol_l = 0.50 if re.search(r"(?:^|[\s/×xX*(])50\s*cl\b", full_txt, re.I) else 0.33
        if m_jfr_any and m_jfr_any.group(2).lower() == "l":
            jfr_l = parse_sv_float(m_jfr_any.group(1).replace(":", ","))
            norm_qty = max(1.0, float(round((price_gross / jfr_l) / can_vol_l))) if jfr_l > 0 else max(1.0, pieces_from)
        elif m_cans:
            cnt = float(m_cans.group(1) or m_cans.group(3))
            norm_qty = cnt if (math.isclose(pieces_from, cnt, abs_tol=0.1) or pieces_from > 4) else cnt * pieces_from
        else:
            norm_qty = max(1.0, pieces_from)
        norm_unit = "st"
        unit_price_net = price_net / norm_qty
    elif slug in ("engangshandskar", "plastpasar_matfilm") and re.search(r"\b(\d{2,3})\s*-?\s*(?:pack|p|st)\b", full_txt, re.I):
        m_hp = re.search(r"\b(\d{2,3})\s*-?\s*(?:pack|p|st)\b", full_txt, re.I)
        per_box = float(m_hp.group(1)) if m_hp else 100.0
        boxes = pieces_from if pieces_from < 20 else 1.0
        norm_qty = boxes * per_box
        norm_unit = "st"
        unit_price_net = price_net / norm_qty
    elif slug == "avokado":
        m_ap = re.search(r"\b(\d+)\s*-?\s*pack\b", full_txt, re.I)
        norm_qty = float(m_ap.group(1)) * (pieces_from if pieces_from <= 4 else 1.0) if m_ap else max(1.0, pieces_from)
        norm_unit = "st"
        unit_price_net = price_net / norm_qty
    else:
        if m_jfr_any:
            jfr_gross = parse_sv_float(m_jfr_any.group(1).replace(":", ","))
            jfr_u_raw = m_jfr_any.group(2).lower()
            norm_unit = "kg" if jfr_u_raw == "kg" else ("L" if jfr_u_raw == "l" else "st")
            if jfr_gross > 0:
                unit_price_net = compute_net_from_gross(jfr_gross, vat_r)
                norm_qty = round(price_gross / jfr_gross, 3)
        elif si_sym == "kg":
            m_exact_g = re.search(r"(?<!ca\s)(?<!ca\.)\b(\d{3})\s*g\b", full_txt, re.I)
            if sz_avg == 1.0 and si_fac == 1.0 and m_exact_g and "ca " not in low_txt and "lösvikt" not in low_txt:
                norm_qty = pieces_from * (float(m_exact_g.group(1)) / 1000.0)
            else:
                norm_qty = max(0.01, pieces_from * sz_avg * si_fac)
            norm_unit = "kg"
            unit_price_net = price_net / norm_qty
        elif si_sym in ("l", "liter"):
            norm_qty = max(0.01, pieces_from * sz_avg * si_fac)
            norm_unit = "L"
            unit_price_net = price_net / norm_qty
        else:
            norm_qty = max(1.0, pieces_from * sz_avg)
            if slug == "gurka" and norm_qty >= 1.0:
                norm_qty = round(norm_qty * 0.35, 3)
                norm_unit = "kg"
            else:
                norm_unit = "st"
            unit_price_net = price_net / norm_qty

    if default_yield < 100.0 and norm_unit == canon_unit:
        unit_price_net = unit_price_net / (default_yield / 100.0)

    v_until = str(offer.get("run_till") or "")[:10]
    images = offer.get("images") or {}
    img_url = str(images.get("view") or images.get("thumb") or "")
    oid = str(offer.get("id") or hashlib.sha1(f"{store_name}:{heading}:{price_gross}".encode()).hexdigest()[:12])

    return {
        "id": oid,
        "slug": slug,
        "canonical_name": b_info["name"],
        "store_name": store_name,
        "heading": heading,
        "price_gross_sek": round(price_gross, 2),
        "norm_unit": norm_unit,
        "unit_price_net_sek": round(unit_price_net, 2),
        "max_limit_note": max_note,
        "valid_until": v_until,
        "image_url": img_url,
    }


def fetch_all_tjek_offers(cfg: Dict[str, Any]) -> List[Dict[str, Any]]:
    lat = cfg.get("lat", 59.237)
    lng = cfg.get("lng", 17.982)
    radius_m = cfg.get("radius_m", 35000)
    allowed_stores = set(cfg.get("stores") or [])

    cat_url = f"https://squid-api.tjek.com/v2/catalogs?r_lat={lat}&r_lng={lng}&r_radius={radius_m}&limit=100"
    req = urllib.request.Request(
        cat_url,
        headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)", "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=15) as resp:
        catalogs = json.loads(resp.read().decode("utf-8"))

    selected: List[Dict[str, Any]] = []
    seen = set()
    for c in catalogs:
        bname = (c.get("branding") or {}).get("name") or ""
        if bname in allowed_stores and bname not in seen and int(c.get("offer_count") or 0) > 0:
            seen.add(bname)
            selected.append(c)

    def _pull(cat_obj: Dict[str, Any]) -> Tuple[str, List[Dict[str, Any]]]:
        cid = cat_obj["id"]
        bname = (cat_obj.get("branding") or {}).get("name") or "Butik"
        out: List[Dict[str, Any]] = []
        for offset in (0, 100, 200):
            u = f"https://squid-api.tjek.com/v2/offers?catalog_ids={urllib.parse.quote(cid)}&limit=100&offset={offset}"
            r = urllib.request.Request(
                u,
                headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)", "Accept": "application/json"},
            )
            with urllib.request.urlopen(r, timeout=15) as res_o:
                batch = json.loads(res_o.read().decode("utf-8"))
            if not batch:
                break
            out.extend(batch)
            if len(batch) < 100:
                break
        return bname, out

    parsed_list: List[Dict[str, Any]] = []
    food_vat = float(cfg.get("food_vat_rate", 6.0))
    non_food = cfg.get("non_food_keywords") or []
    rules = cfg.get("canonical_rules") or []
    baselines = cfg.get("baselines") or {}

    with ThreadPoolExecutor(max_workers=8) as pool:
        futs = [pool.submit(_pull, c) for c in selected]
        for fut in as_completed(futs):
            try:
                bname, offs = fut.result()
                for o in offs:
                    p = normalize_offer(bname, o, food_vat, non_food, rules, baselines)
                    if p:
                        parsed_list.append(p)
            except Exception:
                continue

    return parsed_list


def evaluate_deals(raw_offers: List[Dict[str, Any]], cfg: Dict[str, Any], today_str: str) -> List[Dict[str, Any]]:
    baselines = cfg.get("baselines") or {}
    combined = list(raw_offers) + list(cfg.get("manual_campaigns") or [])
    results: List[Dict[str, Any]] = []

    for item in combined:
        v_until = item.get("valid_until") or ""
        if v_until and v_until < today_str:
            continue

        slug = item.get("slug")
        b = baselines.get(slug) if slug else None
        u_net = float(item["unit_price_net_sek"])

        verdict = "⚪ ÖVRIG VARA"
        verdict_code = "NEUTRAL"
        diff_pct = None
        our_best = None
        canon_unit = item["norm_unit"]

        if b and item["norm_unit"] == b["unit"] and b.get("our_best_price") is not None:
            our_best = float(b["our_best_price"])
            rec_p = float(b.get("record_price") or our_best)
            diff_pct = round((u_net - our_best) / our_best * 100.0, 1) if our_best > 0 else 0.0

            if u_net <= rec_p:
                verdict = "🏆 SLÅR REKORDPRIS!"
                verdict_code = "GREEN"
            elif u_net < our_best * 0.97:
                verdict = "🟢 BILLIGARE ÄN GROSSIST!"
                verdict_code = "GREEN"
            elif u_net <= our_best * 1.05:
                verdict = "🟡 I NIVÅ MED VÅRT PRIS"
                verdict_code = "YELLOW"
            else:
                verdict = "🔴 DYRARE ÄN GROSSIST"
                verdict_code = "RED"

        results.append(
            {
                "id": item["id"],
                "store_name": item["store_name"],
                "heading": item["heading"],
                "canonical_name": item["canonical_name"],
                "price_gross_sek": float(item["price_gross_sek"]),
                "norm_unit": canon_unit,
                "unit_price_net_sek": round(u_net, 2),
                "our_best_price": our_best,
                "diff_pct": diff_pct,
                "verdict": verdict,
                "verdict_code": verdict_code,
                "max_limit_note": item.get("max_limit_note") or "",
                "valid_until": v_until,
                "is_expired": False,
                "image_url": item.get("image_url") or "",
            }
        )

    order_map = {"GREEN": 0, "YELLOW": 1, "NEUTRAL": 2, "RED": 3}
    results.sort(key=lambda x: (order_map.get(x["verdict_code"], 5), x["canonical_name"], x["unit_price_net_sek"]))
    return results


def build_html(payload: Dict[str, Any]) -> str:
    json_blob = json.dumps(payload, ensure_ascii=False).replace("</", "<\\/")
    return f"""<!doctype html>
<html lang="sv">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex,nofollow">
<title>Veckans Rabattlista – Inköp</title>
<style>
  body {{ margin:0; font-family: system-ui, -apple-system, sans-serif; background:#f1f5f9; color:#0f172a; padding-bottom:40px; }}
  .top {{ background:#0f172a; color:#fff; padding:14px 16px; position:sticky; top:0; z-index:20; }}
  .top h1 {{ margin:0; font-size:18px; }}
  .top p {{ margin:3px 0 0; font-size:12px; color:#94a3b8; }}
  .wrap {{ padding:12px; max-width:640px; margin:0 auto; }}
  .filters {{ display:flex; flex-direction:column; gap:8px; margin-bottom:12px; }}
  .search-input {{ width:100%; box-sizing:border-box; padding:10px 12px; border:1px solid #cbd5e1; border-radius:8px; font-size:15px; background:#fff; }}
  .toggle-lbl {{ display:flex; align-items:center; gap:8px; font-size:14px; font-weight:600; background:#fff; padding:9px 11px; border-radius:8px; border:1px solid #cbd5e1; }}
  .chips {{ display:flex; gap:6px; overflow-x:auto; padding-bottom:4px; }}
  .chip {{ border:1px solid #cbd5e1; background:#fff; border-radius:999px; padding:7px 12px; font-size:13px; font-weight:700; white-space:nowrap; cursor:pointer; color:#1e293b; }}
  .chip.active {{ background:#ea580c; color:#fff; border-color:#ea580c; }}
  .card {{ background:#fff; border-radius:12px; padding:12px; margin-bottom:10px; border:1px solid #cbd5e1; display:flex; gap:10px; align-items:flex-start; }}
  .card.green {{ border-left:6px solid #16a34a; background:#f0fdf4; }}
  .card.yellow {{ border-left:6px solid #eab308; }}
  .card.done {{ opacity:0.45; }}
  .thumb {{ width:70px; height:70px; object-fit:contain; background:#fff; border-radius:8px; border:1px solid #e2e8f0; flex-shrink:0; }}
  .info {{ flex:1; min-width:0; }}
  .store-tag {{ display:inline-block; background:#0f172a; color:#fff; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; }}
  .save-tag {{ display:inline-block; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; margin-left:4px; background:#dcfce7; color:#14532d; }}
  .title {{ font-weight:700; font-size:15px; margin:4px 0 2px; }}
  .sub {{ font-size:12px; color:#475569; margin-bottom:4px; }}
  .price-line {{ font-size:14px; font-weight:700; color:#0f172a; }}
  .ref-line {{ font-size:12px; color:#15803d; font-weight:600; margin-top:2px; }}
  .pick-btn {{ border:2px solid #0284c7; background:#fff; color:#0284c7; border-radius:10px; padding:9px 10px; font-weight:700; font-size:13px; cursor:pointer; flex-shrink:0; }}
  .pick-btn.picked {{ background:#16a34a; border-color:#16a34a; color:#fff; }}
</style>
</head>
<body>
<div class="top">
  <h1>🔥 Veckans Rabattlista</h1>
  <p id="metaLbl">Uppdaterad: —</p>
</div>

<div class="wrap">
  <div class="filters">
    <input id="qInput" class="search-input" type="search" placeholder="Sök vara eller butik..." oninput="renderAll()">
    <label class="toggle-lbl">
      <input id="onlyGreen" type="checkbox" checked onchange="renderAll()">
      Visa bara klipp som slår våra grossistpriser
    </label>
    <div class="chips" id="storeChips"></div>
  </div>
  <div id="dealsContainer"></div>
</div>

<script>
const DATA = {json_blob};
let activeStore = 'Alla';
let picked = {{}};
try {{ picked = JSON.parse(localStorage.getItem('kt_cloud_picked') || '{{}}'); }} catch(e) {{}}

function togglePick(key) {{
  picked[key] = !picked[key];
  try {{ localStorage.setItem('kt_cloud_picked', JSON.stringify(picked)); }} catch(e) {{}}
  renderAll();
}}

function renderAll() {{
  const q = (document.getElementById('qInput').value || '').toLowerCase().trim();
  const onlyG = document.getElementById('onlyGreen').checked;
  const baseRows = (DATA.campaigns || []).filter(c => {{
    if (onlyG && c.verdict_code !== 'GREEN') return false;
    if (q && !(c.heading.toLowerCase().includes(q) || c.canonical_name.toLowerCase().includes(q) || c.store_name.toLowerCase().includes(q))) return false;
    return true;
  }});

  const counts = {{}};
  baseRows.forEach(c => {{ counts[c.store_name] = (counts[c.store_name] || 0) + 1; }});
  const stores = ['Alla', ...Object.keys(counts).sort((a, b) => counts[b] - counts[a])];
  if (activeStore !== 'Alla' && !counts[activeStore]) activeStore = 'Alla';

  document.getElementById('metaLbl').textContent =
    `Uppdaterad: ${{DATA.generated_at || ''}} • ${{baseRows.length}} rabatterade klipp`;

  const chipBox = document.getElementById('storeChips');
  chipBox.innerHTML = '';
  stores.forEach(st => {{
    const b = document.createElement('button');
    b.className = 'chip' + (st === activeStore ? ' active' : '');
    b.textContent = st === 'Alla' ? `Alla (${{baseRows.length}})` : `${{st}} (${{counts[st]}})`;
    b.onclick = () => {{ activeStore = st; renderAll(); }};
    chipBox.appendChild(b);
  }});

  const rows = activeStore === 'Alla' ? baseRows : baseRows.filter(c => c.store_name === activeStore);
  const cont = document.getElementById('dealsContainer');
  if (!rows.length) {{
    cont.innerHTML = '<div class="card">Inga rabatter matchar filtret just nu. Avmarkera rutan ovan för att visa alla priser.</div>';
    return;
  }}

  cont.innerHTML = rows.map(c => {{
    const key = 'c_' + c.id;
    const isP = !!picked[key];
    const cls = c.verdict_code === 'GREEN' ? 'green' : (c.verdict_code === 'YELLOW' ? 'yellow' : '');
    const imgHtml = c.image_url ? `<img class="thumb" src="${{c.image_url}}" loading="lazy" alt="">` : '';
    const savePct = (c.diff_pct != null && c.diff_pct < 0) ? ` (${{Math.round(c.diff_pct)}}%)` : '';
    const ourTxt = c.our_best_price != null
      ? `Vårt ordinarie pris: ${{c.our_best_price.toFixed(2)}} kr/${{c.norm_unit}} exkl. moms`
      : '';
    const lim = c.max_limit_note ? ` • ⚠️ ${{c.max_limit_note}}` : '';
    return `<div class="card ${{cls}} ${{isP ? 'done' : ''}}">
      ${{imgHtml}}
      <div class="info">
        <div><span class="store-tag">${{c.store_name}}</span><span class="save-tag">${{c.verdict}}${{savePct}}</span></div>
        <div class="title">${{c.heading}}</div>
        <div class="sub">${{c.canonical_name}} • Gäller t.o.m. ${{c.valid_until || 'söndag'}}${{lim}}</div>
        <div class="price-line">Butikspris: ${{c.price_gross_sek.toFixed(2)}} kr  →  ${{c.unit_price_net_sek.toFixed(2)}} kr/${{c.norm_unit}} exkl. moms</div>
        <div class="ref-line">${{ourTxt}}</div>
      </div>
      <button class="pick-btn ${{isP ? 'picked' : ''}}" onclick="togglePick('${{key}}')">${{isP ? '✓ Klar' : 'Plocka'}}</button>
    </div>`;
  }}).join('');
}}

renderAll();
</script>
</body>
</html>"""


def main() -> None:
    cfg = json.loads(BASELINES_FILE.read_text(encoding="utf-8"))
    now_sv = swedish_now()
    today_str = now_sv.strftime("%Y-%m-%d")

    offers = fetch_all_tjek_offers(cfg)
    deals = evaluate_deals(offers, cfg, today_str)

    payload = {
        "generated_at": now_sv.strftime("%Y-%m-%d %H:%M"),
        "campaigns": deals,
    }
    html = build_html(payload)

    slug_dir = PUBLIC_DIR / str(cfg.get("secret_slug") or "lista")
    slug_dir.mkdir(parents=True, exist_ok=True)
    (PUBLIC_DIR / ".nojekyll").write_text("", encoding="utf-8")
    (PUBLIC_DIR / "index.html").write_text(
        "<!doctype html><html><head><meta name='robots' content='noindex'></head><body>OK</body></html>",
        encoding="utf-8",
    )
    (slug_dir / "index.html").write_text(html, encoding="utf-8")
    print(f"Klart! Byggde {len(deals)} kampanjer ({sum(1 for d in deals if d['verdict_code'] == 'GREEN')} gröna klipp) -> {slug_dir / 'index.html'}")


if __name__ == "__main__":
    main()
