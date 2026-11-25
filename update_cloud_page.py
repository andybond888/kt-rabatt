"""
Självgående molnskript (update_cloud_page.py) – körs automatiskt i GitHub Actions varje morgon
(och lokalt vid publicering) helt utan externa paket.
Hämtar aktuella reklamblad runt Huddinge/Söderort, jämför mot baselines.json och bygger mobilrabattlistan
med full filtrering på varor, kategorier och butiker.
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
    utc_now = datetime.now(timezone.utc)
    offset_h = 2 if 4 <= utc_now.month <= 10 else 1
    return utc_now + timedelta(hours=offset_h)


GLOBAL_HEADING_EXCLUSIONS = (
    "pastry",
    "gyoza skin",
    "wonton pastry",
    "finkrossade",
    "krossade tomat",
    "passerade tomat",
    "tomater på burk",
    "tomatpur",
    "leverpastej",
    "salami",
    "smörgåspålägg",
    "skaldjursbricka",
    "umamifärs",
    "svartrökt",
    "flytande smör",
    "lammrostbiff",
    "inlagda grönsaker",
    "mixpickles",
    "arter/morotter",
    "ärtor/morötter",
)


def match_slug(text: str, rules: List[Dict[str, Any]]) -> Optional[str]:
    low = re.sub(r"\s+", " ", (text or "")).lower().strip()
    if not low or low == "pant" or low.startswith("pant ") or "rabatt" in low:
        return None
    if any(x in low for x in GLOBAL_HEADING_EXCLUSIONS):
        return None
    for rule in rules:
        negs = rule.get("negatives") or []
        if negs and any(n in low for n in negs):
            continue
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
            "kex",
            "kaka",
            "hund",
            "katt",
            "smörgåspålägg",
            "skaldjursbricka",
            "porchetta",
            "kebab",
            "panerade",
        )
    ):
        slug = None
    if slug and slug != "vaniljglass_storpack" and "glass" in low_txt:
        slug = None

    if slug:
        rule_obj = next((r for r in rules if r["slug"] == slug), None)
        if rule_obj and any(n in low_txt for n in (rule_obj.get("negatives") or [])):
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
    elif slug in ("agg", "engangshandskar", "avfallspasar_sopsackar", "sopsackar_stora", "plastpasar_matfilm", "maskindiskmedel") and re.search(
        r"\b(\d{1,3})\s*-?\s*(?:pack|p|st|tab)\b", full_txt, re.I
    ):
        m_hp = re.search(r"\b(\d{1,3})\s*-?\s*(?:pack|p|st|tab)\b", full_txt, re.I)
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
            elif canon_unit == "L":
                m_lit = re.search(r"\b(\d+(?:[.,]\d+)?)\s*(?:l|liter)\b", full_txt, re.I)
                m_dl = re.search(r"\b(\d+(?:[.,]\d+)?)\s*dl\b", full_txt, re.I)
                per_p = parse_sv_float(m_lit.group(1)) if m_lit else (parse_sv_float(m_dl.group(1)) / 10.0 if m_dl else 1.0)
                norm_qty = round(max(0.1, pieces_from * (per_p if per_p > 0 else 1.0)), 3)
                norm_unit = "L"
            else:
                norm_unit = "st"
            unit_price_net = price_net / norm_qty

    if slug == "vaniljglass_storpack" and (norm_unit != "L" or norm_qty < 0.8):
        return None

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
        "category": b_info.get("category") or "Övrigt",
        "store_name": store_name,
        "heading": heading,
        "description": re.sub(r"\s+", " ", desc),
        "price_gross_sek": round(price_gross, 2),
        "norm_qty": round(norm_qty, 3),
        "norm_unit": norm_unit,
        "vat_rate": vat_r,
        "unit_price_net_sek": round(unit_price_net, 2),
        "unit_price_gross_sek": round(unit_price_net * (1.0 + vat_r / 100.0), 2),
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
        cat_name = item.get("category") or (b.get("category") if b else "Övrigt") or "Övrigt"

        if b and item["norm_unit"] == b["unit"] and b.get("our_best_price") is not None:
            our_best = float(b["our_best_price"])
            rec_p = float(b.get("record_price") or our_best)
            diff_pct = round((u_net - our_best) / our_best * 100.0, 1) if our_best > 0 else 0.0

            if u_net <= rec_p:
                verdict = "🏆 SLÅR REKORDPRIS!"
                verdict_code = "GREEN"
            elif u_net < our_best * 0.97:
                verdict = "🟢 BILLIGARE ÄN VÅRT PRIS!"
                verdict_code = "GREEN"
            elif u_net <= our_best * 1.05:
                verdict = "🟡 I NIVÅ MED VÅRT PRIS"
                verdict_code = "YELLOW"
            else:
                verdict = "🔴 DYRARE ÄN VÅRT PRIS"
                verdict_code = "RED"

        vat_r = float(item.get("vat_rate") or cfg.get("food_vat_rate", 6.0))
        u_gross = round(
            float(item["unit_price_gross_sek"])
            if item.get("unit_price_gross_sek") is not None
            else u_net * (1.0 + vat_r / 100.0),
            2,
        )
        our_best_gross = round(our_best * (1.0 + vat_r / 100.0), 2) if our_best is not None else None
        raw_hist = (b.get("history") if b else []) or []
        hist_gross = [
            {
                "date": h.get("date") or "",
                "supplier": h.get("supplier") or "",
                "price_gross": round(float(h.get("price_net") or 0.0) * (1.0 + vat_r / 100.0), 2),
                "unit": h.get("unit") or canon_unit,
            }
            for h in raw_hist
            if float(h.get("price_net") or 0.0) > 0 and (h.get("unit") or canon_unit) == canon_unit
        ][:8]
        ref_source = str((b.get("ref_source") if b else "") or ("butik" if hist_gross else "riktpris"))

        results.append(
            {
                "id": item["id"],
                "store_name": item["store_name"],
                "heading": item["heading"],
                "description": item.get("description") or "",
                "canonical_name": item["canonical_name"],
                "category": cat_name,
                "price_gross_sek": float(item["price_gross_sek"]),
                "norm_qty": float(item.get("norm_qty") or 1.0),
                "norm_unit": canon_unit,
                "vat_rate": vat_r,
                "unit_price_net_sek": round(u_net, 2),
                "unit_price_gross_sek": u_gross,
                "our_best_price": our_best,
                "our_best_price_gross": our_best_gross,
                "ref_source": ref_source,
                "history": hist_gross,
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
    results.sort(key=lambda x: (order_map.get(x["verdict_code"], 5), x["diff_pct"] if x["diff_pct"] is not None else 999.0, x["unit_price_net_sek"]))
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
  body {{ margin:0; font-family: system-ui, -apple-system, sans-serif; background:#f1f5f9; color:#0f172a; padding-bottom:44px; }}
  .top {{ background:#0f172a; color:#fff; padding:14px 16px; position:sticky; top:0; z-index:20; }}
  .top h1 {{ margin:0; font-size:18px; }}
  .top p {{ margin:3px 0 0; font-size:12px; color:#94a3b8; }}
  .wrap {{ padding:12px; max-width:660px; margin:0 auto; }}
  .filters {{ display:flex; flex-direction:column; gap:8px; margin-bottom:12px; }}
  .row-flex {{ display:flex; gap:8px; align-items:center; }}
  .search-input {{ flex:1; box-sizing:border-box; padding:10px 12px; border:1px solid #cbd5e1; border-radius:8px; font-size:15px; background:#fff; }}
  .cfg-btn {{ border:1px solid #0f172a; background:#fff; color:#0f172a; border-radius:8px; padding:10px 11px; font-weight:700; font-size:13px; cursor:pointer; white-space:nowrap; }}
  .cfg-btn.active {{ background:#0f172a; color:#fff; }}
  .prod-select {{ width:100%; padding:10px 12px; border:1px solid #cbd5e1; border-radius:8px; font-size:14px; font-weight:600; background:#fff; color:#0f172a; }}
  .toggle-lbl {{ display:flex; align-items:center; gap:8px; font-size:14px; font-weight:600; background:#fff; padding:9px 11px; border-radius:8px; border:1px solid #cbd5e1; }}
  .sec-lbl {{ font-size:11px; font-weight:700; color:#475569; text-transform:uppercase; letter-spacing:0.4px; margin-top:2px; }}
  .chips {{ display:flex; gap:6px; overflow-x:auto; padding-bottom:4px; }}
  .chip {{ border:1px solid #cbd5e1; background:#fff; border-radius:999px; padding:6px 12px; font-size:13px; font-weight:700; white-space:nowrap; cursor:pointer; color:#1e293b; }}
  .chip.active {{ background:#ea580c; color:#fff; border-color:#ea580c; }}
  .chip.cat-chip.active {{ background:#0284c7; color:#fff; border-color:#0284c7; }}
  .varu-panel {{ display:none; background:#fff; border:1px solid #cbd5e1; border-radius:10px; padding:12px; margin-bottom:6px; }}
  .varu-panel.open {{ display:block; }}
  .varu-grid {{ display:grid; grid-template-columns:repeat(auto-fill, minmax(175px, 1fr)); gap:6px; max-height:260px; overflow-y:auto; margin-top:8px; }}
  .varu-chk {{ display:flex; align-items:center; gap:6px; font-size:13px; padding:5px 7px; border-radius:6px; background:#f8fafc; border:1px solid #e2e8f0; }}
  .mini-btn {{ border:1px solid #cbd5e1; background:#f1f5f9; border-radius:6px; padding:5px 10px; font-size:12px; font-weight:700; cursor:pointer; }}
  .card {{ background:#fff; border-radius:12px; padding:12px; margin-bottom:10px; border:1px solid #cbd5e1; display:flex; gap:10px; align-items:flex-start; }}
  .card.green {{ border-left:6px solid #16a34a; background:#f0fdf4; }}
  .card.yellow {{ border-left:6px solid #eab308; }}
  .card.done {{ opacity:0.45; }}
  .thumb {{ width:70px; height:70px; object-fit:contain; background:#fff; border-radius:8px; border:1px solid #e2e8f0; flex-shrink:0; }}
  .info {{ flex:1; min-width:0; }}
  .store-tag {{ display:inline-block; background:#0f172a; color:#fff; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; }}
  .loc-tag {{ display:inline-block; background:#fef3c7; color:#92400e; font-size:11px; font-weight:600; padding:2px 7px; border-radius:5px; margin-left:4px; text-decoration:none; }}
  .loc-tag:hover {{ background:#fde68a; }}
  .route-tag {{ display:inline-block; background:#ede9fe; color:#5b21b6; font-size:11px; font-weight:600; padding:2px 7px; border-radius:5px; margin-left:4px; text-decoration:none; }}
  .route-tag:hover {{ background:#ddd6fe; }}
  .cat-tag {{ display:inline-block; background:#e0f2fe; color:#0369a1; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; margin-left:4px; }}
  .save-tag {{ display:inline-block; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; margin-left:4px; background:#dcfce7; color:#14532d; }}
  .title {{ font-weight:700; font-size:15px; margin:4px 0 2px; }}
  .sub {{ font-size:12px; color:#475569; margin-bottom:4px; }}
  .price-line {{ display:flex; flex-wrap:wrap; align-items:baseline; gap:6px; margin-top:4px; }}
  .price-main {{ font-size:17px; font-weight:800; color:#0f172a; }}
  .price-qty {{ font-size:12px; font-weight:600; color:#475569; }}
  .price-unit {{ font-size:12px; font-weight:700; color:#0369a1; background:#f0f9ff; border:1px solid #bae6fd; padding:1px 7px; border-radius:999px; }}
  .ref-line {{ font-size:12px; color:#15803d; font-weight:600; margin-top:3px; }}
  .pick-btn {{ border:2px solid #0284c7; background:#fff; color:#0284c7; border-radius:10px; padding:9px 10px; font-weight:700; font-size:13px; cursor:pointer; width:100%; }}
  .pick-btn.picked {{ background:#16a34a; border-color:#16a34a; color:#fff; }}
  .actions {{ display:flex; flex-direction:column; gap:6px; flex-shrink:0; min-width:86px; }}
  .hist-btn {{ border:1px solid #cbd5e1; background:#f8fafc; color:#334155; border-radius:8px; padding:6px 8px; font-weight:600; font-size:12px; cursor:pointer; width:100%; }}
  .hist-btn.open {{ background:#0f172a; color:#fff; border-color:#0f172a; }}
  .hist-box {{ margin-top:8px; padding:8px 10px; background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; font-size:12px; color:#334155; }}
  .hist-row {{ display:flex; justify-content:space-between; padding:2px 0; border-bottom:1px dashed #e2e8f0; }}
  .hist-row:last-child {{ border-bottom:none; }}
</style>
</head>
<body>
<div class="top">
  <h1>🔥 Veckans Rabattlista</h1>
  <p id="metaLbl">Uppdaterad: —</p>
</div>

<div class="wrap">
  <div class="filters">
    <div class="row-flex">
      <input id="qInput" class="search-input" type="search" placeholder="Sök vara eller butik..." oninput="renderAll()">
      <button id="btnVaror" class="cfg-btn" onclick="toggleVaruPanel()">⚙️ Välj varor</button>
    </div>

    <div class="row-flex">
      <select id="originSelect" class="prod-select" style="flex:1" onchange="onOriginSelect()">
        <option value="Arrendatorsvägen 1, 141 62 Huddinge">📍 Start: Arrendatorsvägen 1, 141 62 Huddinge</option>
        <option value="Skanstull, Stockholm">🏠 Start: Skanstull, Stockholm</option>
        <option value="__custom__">✏️ Annan startadress...</option>
      </select>
    </div>
    <div id="customOriginRow" class="row-flex" style="display:none">
      <input id="originInput" class="search-input" type="text" placeholder="Skriv egen startadress..." oninput="onOriginChange()">
    </div>

    <div id="varuPanel" class="varu-panel">
      <div style="display:flex;justify-content:space-between;align-items:center;gap:6px;flex-wrap:wrap">
        <strong style="font-size:13px">Kryssa i vilka varor du vill se i listan:</strong>
        <div style="display:flex;gap:6px">
          <button class="mini-btn" onclick="setAllHidden(false)">Visa alla</button>
          <button class="mini-btn" onclick="setAllHidden(true)">Avmarkera alla</button>
        </div>
      </div>
      <div id="varuGrid" class="varu-grid"></div>
    </div>

    <select id="prodSelect" class="prod-select" onchange="onProdSelect()">
      <option value="Alla">Alla valda varor</option>
    </select>

    <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center">
      <label class="toggle-lbl">
        <input id="onlyGreen" type="checkbox" checked onchange="renderAll()">
        Visa bara klipp som slår våra priser
      </label>
      <div class="chips" id="areaChips" style="padding-bottom:0"></div>
    </div>

    <div class="sec-lbl">Kategori</div>
    <div class="chips" id="catChips"></div>

    <div class="sec-lbl">Butik</div>
    <div class="chips" id="storeChips"></div>
  </div>
  <div id="dealsContainer"></div>
</div>

<script>
const DATA = {json_blob};
let activeCat = 'Alla';
let activeStore = 'Alla';
let activeProd = 'Alla';
let picked = {{}};
let hiddenProds = {{}};
try {{ picked = JSON.parse(localStorage.getItem('kt_cloud_picked') || '{{}}'); }} catch(e) {{}}
try {{ hiddenProds = JSON.parse(localStorage.getItem('kt_cloud_hidden_prods') || '{{}}'); }} catch(e) {{}}

function toggleVaruPanel() {{
  const p = document.getElementById('varuPanel');
  const b = document.getElementById('btnVaror');
  p.classList.toggle('open');
  b.classList.toggle('active');
}}

function toggleHiddenProd(pName, checked) {{
  if (checked) delete hiddenProds[pName];
  else hiddenProds[pName] = true;
  try {{ localStorage.setItem('kt_cloud_hidden_prods', JSON.stringify(hiddenProds)); }} catch(e) {{}}
  renderAll();
}}

function setAllHidden(hideAll) {{
  hiddenProds = {{}};
  if (hideAll) {{
    (DATA.campaigns || []).forEach(c => {{ hiddenProds[c.canonical_name] = true; }});
  }}
  try {{ localStorage.setItem('kt_cloud_hidden_prods', JSON.stringify(hiddenProds)); }} catch(e) {{}}
  buildVaruCheckboxes();
  renderAll();
}}

function buildVaruCheckboxes() {{
  const allNames = Array.from(new Set((DATA.campaigns || []).map(c => c.canonical_name))).sort((a, b) => a.localeCompare(b, 'sv'));
  const grid = document.getElementById('varuGrid');
  grid.innerHTML = '';
  allNames.forEach(nm => {{
    const lbl = document.createElement('label');
    lbl.className = 'varu-chk';
    const chk = document.createElement('input');
    chk.type = 'checkbox';
    chk.checked = !hiddenProds[nm];
    chk.onchange = () => toggleHiddenProd(nm, chk.checked);
    const sp = document.createElement('span');
    sp.textContent = nm;
    lbl.appendChild(chk);
    lbl.appendChild(sp);
    grid.appendChild(lbl);
  }});
}}

function onProdSelect() {{
  activeProd = document.getElementById('prodSelect').value || 'Alla';
  renderAll();
}}

let openHist = {{}};
function toggleHist(key) {{
  openHist[key] = !openHist[key];
  renderAll();
}}

function togglePick(key) {{
  picked[key] = !picked[key];
  try {{ localStorage.setItem('kt_cloud_picked', JSON.stringify(picked)); }} catch(e) {{}}
  renderAll();
}}

const STORE_LOCATIONS = {{
  "City Gross": ["Länna (19 min)", "Kungens Kurva (21 min)"],
  "Coop": ["Huddinge (3 min)", "Stuvsta (6 min)"],
  "Costco": ["Arninge, Täby (35 min)"],
  "Din Mat": ["Skärholmen (19 min)", "Alby (23 min)"],
  "DollarStore": ["Kungens Kurva (18 min)"],
  "Hemköp": ["Huddinge (3 min)", "Skanstull (20 min)"],
  "ICA Kvantum": ["Farsta (17 min)", "Skanstull (20 min)"],
  "ICA Maxi Stormarknad": ["Flemingsberg (9 min)", "Haninge (24 min)"],
  "ICA Nära": ["Segeltorp (14 min)", "Huddinge (18 min)"],
  "ICA Supermarket": ["Huddinge (2 min)", "Stuvsta (7 min)"],
  "Lidl": ["Rågsved (7 min)", "Huddinge (10 min)"],
  "Matcenter": ["Alby (18 min)"],
  "Matdax": ["Högdalen (10 min)", "Hökarängen (15 min)"],
  "Matvärlden": ["Kungens Kurva (18 min)"],
  "Nya Pulsen": ["Flemingsberg (10 min)"],
  "Rusta": ["Länna (20 min)", "Kungens Kurva (20 min)"],
  "Stora Coop": ["Huddinge (3 min)", "Västberga (14 min)"],
  "Supergrossen": ["Vårby (17 min)", "Skärholmen (19 min)"],
  "Willys": ["Flemingsberg (10 min)", "Länna (19 min)"],
  "Willys Hemma": ["Älvsjö (10 min)", "Huddinge (14 min)"],
  "ÖoB": ["Skärholmen (19 min)", "Haninge (22 min)"]
}};

const FAR_STORES = new Set([
  "City Gross", "Costco", "Din Mat", "DollarStore", "ICA Kvantum",
  "ICA Nära", "Matcenter", "Matvärlden", "Rusta", "Supergrossen", "ÖoB"
]);
const ROUTE_STORES = new Set([
  "ICA Kvantum", "Hemköp", "Lidl", "Matdax", "Stora Coop",
  "Willys Hemma", "Coop", "ICA Supermarket", "ICA Nära"
]);
const ROUTE_TIMES = {{
  "City Gross": "33 min",
  "Coop": "20 min",
  "Costco": "63 min",
  "Din Mat": "29 min",
  "DollarStore": "30 min",
  "Hemköp": "21 min",
  "ICA Kvantum": "27 min",
  "ICA Maxi Stormarknad": "30 min",
  "ICA Nära": "32 min",
  "ICA Supermarket": "18 min",
  "Lidl": "19 min",
  "Matcenter": "37 min",
  "Matdax": "23 min",
  "Matvärlden": "31 min",
  "Nya Pulsen": "32 min",
  "Rusta": "33 min",
  "Stora Coop": "20 min",
  "Supergrossen": "29 min",
  "Willys": "30 min",
  "Willys Hemma": "23 min",
  "ÖoB": "29 min"
}};
let activeArea = 'near';
const DEFAULT_ORIGIN = 'Arrendatorsvägen 1, 141 62 Huddinge';
const PRESET_ORIGINS = new Set(['Arrendatorsvägen 1, 141 62 Huddinge', 'Skanstull, Stockholm']);
let userOrigin = DEFAULT_ORIGIN;
try {{ userOrigin = localStorage.getItem('kt_cloud_origin') || DEFAULT_ORIGIN; }} catch(e) {{}}
if (PRESET_ORIGINS.has(userOrigin)) {{
  document.getElementById('originSelect').value = userOrigin;
}} else {{
  document.getElementById('originSelect').value = '__custom__';
  document.getElementById('customOriginRow').style.display = 'flex';
  document.getElementById('originInput').value = userOrigin;
}}

function onOriginSelect() {{
  const val = document.getElementById('originSelect').value;
  const row = document.getElementById('customOriginRow');
  if (val === '__custom__') {{
    row.style.display = 'flex';
    document.getElementById('originInput').focus();
    userOrigin = (document.getElementById('originInput').value || '').trim() || DEFAULT_ORIGIN;
  }} else {{
    row.style.display = 'none';
    userOrigin = val;
    try {{ localStorage.setItem('kt_cloud_origin', userOrigin); }} catch(e) {{}}
  }}
  renderAll();
}}

function onOriginChange() {{
  userOrigin = (document.getElementById('originInput').value || '').trim() || DEFAULT_ORIGIN;
  try {{ localStorage.setItem('kt_cloud_origin', userOrigin); }} catch(e) {{}}
  renderAll();
}}

const STORE_LOCATIONS_SKANSTULL = {{
  "City Gross": ["Länna (14 min)", "Kungens Kurva (14 min)"],
  "Coop": ["Stuvsta (13 min)", "Huddinge (17 min)"],
  "Costco": ["Arninge, Täby (26 min)"],
  "Din Mat": ["Skärholmen (12 min)", "Alby (21 min)"],
  "DollarStore": ["Kungens Kurva (12 min)"],
  "Hemköp": ["Skanstull (5 min)", "Huddinge (17 min)"],
  "ICA Kvantum": ["Skanstull (1 min)", "Farsta (9 min)"],
  "ICA Maxi Stormarknad": ["Haninge (17 min)", "Flemingsberg (20 min)"],
  "ICA Nära": ["Segeltorp (11 min)", "Huddinge (12 min)"],
  "ICA Supermarket": ["Stuvsta (14 min)", "Huddinge (15 min)"],
  "Lidl": ["Rågsved (12 min)", "Huddinge (21 min)"],
  "Matcenter": ["Alby (18 min)"],
  "Matdax": ["Hökarängen (8 min)", "Högdalen (12 min)"],
  "Matvärlden": ["Kungens Kurva (14 min)"],
  "Nya Pulsen": ["Flemingsberg (21 min)"],
  "Rusta": ["Länna (13 min)", "Kungens Kurva (13 min)"],
  "Stora Coop": ["Västberga (8 min)", "Huddinge (17 min)"],
  "Supergrossen": ["Skärholmen (12 min)", "Vårby (17 min)"],
  "Willys": ["Länna (13 min)", "Flemingsberg (21 min)"],
  "Willys Hemma": ["Älvsjö (10 min)", "Huddinge (27 min)"],
  "ÖoB": ["Skärholmen (12 min)", "Haninge (16 min)"]
}};

function storeLocs(name) {{
  if (userOrigin === 'Skanstull, Stockholm') return STORE_LOCATIONS_SKANSTULL[name] || [];
  if (userOrigin === DEFAULT_ORIGIN) return STORE_LOCATIONS[name] || [];
  return (STORE_LOCATIONS[name] || []).map(l => l.replace(/\\s*\\([^)]*\\)/g, '').trim());
}}

function storeLoc(name) {{
  return storeLocs(name).join(' ');
}}

function renderAll() {{
  const areaBox = document.getElementById('areaChips');
  const areaOpts = [
    ['near', '📍 Nära Arrendatorsvägen'],
    ['route', '🚗 Skanstull → Jobbet'],
    ['all', '🗺️ Alla butiker']
  ];
  areaBox.innerHTML = '';
  areaOpts.forEach(([val, lbl]) => {{
    const b = document.createElement('button');
    b.className = 'chip cat-chip' + (activeArea === val ? ' active' : '');
    b.textContent = lbl;
    b.onclick = () => {{ activeArea = val; renderAll(); }};
    areaBox.appendChild(b);
  }});

  const q = (document.getElementById('qInput').value || '').toLowerCase().trim();
  const onlyG = document.getElementById('onlyGreen').checked;

  const visibleBase = (DATA.campaigns || []).filter(c => {{
    if (hiddenProds[c.canonical_name]) return false;
    if (onlyG && c.verdict_code !== 'GREEN') return false;
    if (activeArea === 'near' && FAR_STORES.has(c.store_name)) return false;
    if (activeArea === 'route' && !ROUTE_STORES.has(c.store_name)) return false;
    const loc = storeLoc(c.store_name).toLowerCase();
    if (q && !(c.heading.toLowerCase().includes(q) || c.canonical_name.toLowerCase().includes(q) || (c.category || '').toLowerCase().includes(q) || c.store_name.toLowerCase().includes(q) || loc.includes(q))) return false;
    return true;
  }});

  const catCounts = {{}};
  visibleBase.forEach(c => {{
    const cat = c.category || 'Övrigt';
    catCounts[cat] = (catCounts[cat] || 0) + 1;
  }});
  if (activeCat !== 'Alla' && !catCounts[activeCat]) activeCat = 'Alla';
  const cats = ['Alla', ...Object.keys(catCounts).sort((a, b) => catCounts[b] - catCounts[a])];
  const catBox = document.getElementById('catChips');
  catBox.innerHTML = '';
  cats.forEach(ct => {{
    const b = document.createElement('button');
    b.className = 'chip cat-chip' + (ct === activeCat ? ' active' : '');
    b.textContent = ct === 'Alla' ? `Alla (${{visibleBase.length}})` : `${{ct}} (${{catCounts[ct]}})`;
    b.onclick = () => {{ activeCat = ct; activeProd = 'Alla'; renderAll(); }};
    catBox.appendChild(b);
  }});

  const afterCat = activeCat === 'Alla' ? visibleBase : visibleBase.filter(c => (c.category || 'Övrigt') === activeCat);

  const prodCounts = {{}};
  afterCat.forEach(c => {{ prodCounts[c.canonical_name] = (prodCounts[c.canonical_name] || 0) + 1; }});
  if (activeProd !== 'Alla' && !prodCounts[activeProd]) activeProd = 'Alla';
  const sel = document.getElementById('prodSelect');
  const sortedProds = Object.keys(prodCounts).sort((a, b) => a.localeCompare(b, 'sv'));
  sel.innerHTML = `<option value="Alla">Alla varor i urvalet (${{sortedProds.length}} varutyper)</option>` +
    sortedProds.map(p => `<option value="${{p.replace(/"/g, '&quot;')}}" ${{p === activeProd ? 'selected' : ''}}>${{p}} (${{prodCounts[p]}} klipp)</option>`).join('');

  const afterProd = activeProd === 'Alla' ? afterCat : afterCat.filter(c => c.canonical_name === activeProd);

  const stCounts = {{}};
  afterProd.forEach(c => {{ stCounts[c.store_name] = (stCounts[c.store_name] || 0) + 1; }});
  if (activeStore !== 'Alla' && !stCounts[activeStore]) activeStore = 'Alla';
  const stores = ['Alla', ...Object.keys(stCounts).sort((a, b) => stCounts[b] - stCounts[a])];
  const chipBox = document.getElementById('storeChips');
  chipBox.innerHTML = '';
  stores.forEach(st => {{
    const b = document.createElement('button');
    b.className = 'chip' + (st === activeStore ? ' active' : '');
    const locs = storeLocs(st);
    const shortLoc = locs.length ? locs[0].replace(/\\s*\\([^)]*\\)/g, '').trim() : '';
    b.textContent = st === 'Alla' ? `Alla butiker (${{afterProd.length}})` : `${{st}}${{shortLoc ? ' · ' + shortLoc : ''}} (${{stCounts[st]}})`;
    b.onclick = () => {{ activeStore = st; renderAll(); }};
    chipBox.appendChild(b);
  }});

  const rows = activeStore === 'Alla' ? afterProd : afterProd.filter(c => c.store_name === activeStore);
  const hiddenCnt = Object.keys(hiddenProds).length;
  const hiddenNote = hiddenCnt > 0 ? ` • ${{hiddenCnt}} bortfiltrerade varor` : '';
  document.getElementById('metaLbl').textContent =
    `Uppdaterad: ${{DATA.generated_at || ''}} • ${{rows.length}} rabatterade klipp${{hiddenNote}}`;

  const cont = document.getElementById('dealsContainer');
  if (!rows.length) {{
    cont.innerHTML = '<div class="card">Inga rabatter matchar filtret just nu. Justera varu-/kategorifiltret eller avmarkera rutan ovan för att visa alla priser.</div>';
    return;
  }}

  cont.innerHTML = rows.map(c => {{
    const key = 'c_' + c.id;
    const isP = !!picked[key];
    const cls = c.verdict_code === 'GREEN' ? 'green' : (c.verdict_code === 'YELLOW' ? 'yellow' : '');
    const imgHtml = c.image_url ? `<img class="thumb" src="${{c.image_url}}" loading="lazy" alt="">` : '';
    const savePct = (c.diff_pct != null && c.diff_pct < 0) ? ` (${{Math.round(c.diff_pct)}}%)` : '';
    const unitGross = c.unit_price_gross_sek != null ? c.unit_price_gross_sek : (c.unit_price_net_sek * (1 + (c.vat_rate || 6) / 100));
    const ourGross = c.our_best_price_gross != null ? c.our_best_price_gross : (c.our_best_price != null ? c.our_best_price * (1 + (c.vat_rate || 6) / 100) : null);
    const refLbl = c.ref_source === 'grossist'
      ? 'Vårt grossistpris'
      : (c.ref_source === 'butik' ? 'Vårt snittpris (butik)' : 'Riktpris (saknar egna köp)');
    const fmtKr = (v, dropZero) => {{
      const n = Number(v || 0);
      if (dropZero && Math.abs(n - Math.round(n)) < 0.005) return `${{Math.round(n)}} kr`;
      return `${{n.toFixed(2).replace('.', ',')}} kr`;
    }};
    const fmtQty = (q) => String(Number((q || 1).toFixed(2))).replace('.', ',');
    const qtyVal = Number(c.norm_qty || 1);
    const samePrice = Math.abs(qtyVal - 1) < 0.01 && Math.abs(c.price_gross_sek - unitGross) < 0.05;
    const priceBlockHtml = samePrice
      ? `<span class="price-main">${{fmtKr(c.price_gross_sek, true)}}/${{c.norm_unit}}</span><span class="price-qty">inkl. moms</span>`
      : `<span class="price-main">${{fmtKr(c.price_gross_sek, true)}}</span><span class="price-qty">för ${{fmtQty(qtyVal)}} ${{c.norm_unit}}</span><span class="price-unit">${{fmtKr(unitGross, false)}}/${{c.norm_unit}}</span>`;
    const ourTxt = ourGross != null
      ? `${{refLbl}}: ${{fmtKr(ourGross, false)}}/${{c.norm_unit}} inkl. moms`
      : '';
    const lim = c.max_limit_note ? ` • ⚠️ ${{c.max_limit_note}}` : '';
    const descShort = c.description ? (c.description.length > 78 ? c.description.slice(0, 75) + '…' : c.description) : '';
    const hist = c.history || [];
    const isH = !!openHist[key];
    const histBtnHtml = hist.length
      ? `<button class="hist-btn ${{isH ? 'open' : ''}}" onclick="toggleHist('${{key}}')">📈 Historik</button>`
      : '';
    const histHtml = (isH && hist.length)
      ? `<div class="hist-box"><div style="font-weight:700;margin-bottom:4px;">Senaste inköpspriser (${{c.canonical_name}}, inkl. moms):</div>` +
        hist.map(h => `<div class="hist-row"><span>${{h.date}}${{h.supplier ? ' • ' + h.supplier : ''}}</span><b>${{Number(h.price_gross).toFixed(2)}} kr/${{h.unit}}</b></div>`).join('') +
        `</div>`
      : '';
    const locs = storeLocs(c.store_name);
    const homeAddr = userOrigin || DEFAULT_ORIGIN;
    const locPills = locs.map(l => {{
      const cleanD = l.replace(/\\s*\\([^)]*\\)/g, '').trim();
      const qDest = c.store_name + (cleanD ? ' ' + cleanD : '');
      const uDir = `https://www.google.com/maps/dir/?api=1&origin=${{encodeURIComponent(homeAddr)}}&destination=${{encodeURIComponent(qDest)}}`;
      return `<a class="loc-tag" href="${{uDir}}" target="_blank" rel="noopener">📍 ${{l}}</a>`;
    }}).join('');
    const firstClean = locs.length ? locs[0].replace(/\\s*\\([^)]*\\)/g, '').trim() : '';
    const firstQuery = c.store_name + (firstClean ? ' ' + firstClean : '');
    const hemvagUrl = locs.length ? `https://www.google.com/maps/dir/?api=1&origin=${{encodeURIComponent('Skanstull, Stockholm')}}&waypoints=${{encodeURIComponent(firstQuery)}}&destination=${{encodeURIComponent(homeAddr)}}` : '';
    const rtTime = ROUTE_TIMES[c.store_name] ? ` (${{ROUTE_TIMES[c.store_name]}})` : '';
    const locHtml = locs.length ? `${{locPills}}<a class="route-tag" href="${{hemvagUrl}}" target="_blank" rel="noopener" title="Skanstull → ${{c.store_name}} → Arrendatorsvägen">🚗 Till jobbet${{rtTime}}</a>` : '';
    return `<div class="card ${{cls}} ${{isP ? 'done' : ''}}">
      ${{imgHtml}}
      <div class="info">
        <div><span class="store-tag">${{c.store_name}}</span>${{locHtml}}<span class="cat-tag">${{c.category || 'Basvara'}}</span><span class="save-tag">${{c.verdict}}${{savePct}}</span></div>
        <div class="title">${{c.heading}}</div>
        ${{descShort ? `<div class="sub" style="color:#334155">${{descShort}}</div>` : ''}}
        <div class="sub">${{c.canonical_name}} • Gäller t.o.m. ${{c.valid_until || 'söndag'}}${{lim}}</div>
        <div class="price-line">${{priceBlockHtml}}</div>
        <div class="ref-line">${{ourTxt}}</div>
        ${{histHtml}}
      </div>
      <div class="actions">
        <button class="pick-btn ${{isP ? 'picked' : ''}}" onclick="togglePick('${{key}}')">${{isP ? '✓ Klar' : 'Plocka'}}</button>
        ${{histBtnHtml}}
      </div>
    </div>`;
  }}).join('');
}}

buildVaruCheckboxes();
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
