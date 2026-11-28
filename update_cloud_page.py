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


GENERAL_CATEGORIES = (
    ("Kött & Chark", ("skinka", "julskinka", "korv", "salami", "kött", "kyckling", "kalkon", "bacon", "färs", "kotlett", "karré", "entrecôte", "ryggbiff", "oxfilé", "fläsk", "lamm", "leverpastej", "pålägg", "revben", "köttbull", "prinskorv")),
    ("Fisk & Skaldjur", ("lax", "torsk", "sill", "räkor", "kräftor", "tonfisk", "fisk", "makrill", "skaldjur", "musslor", "kaviar", "rom")),
    ("Frukt & Grönt", ("äpple", "päron", "kaki", "apelsin", "clementin", "klementin", "satsumas", "banan", "druvor", "melon", "mango", "ananas", "kiwi", "avokado", "tomat", "gurka", "paprika", "sallad", "lök", "potatis", "morot", "morötter", "broccoli", "kål", "svamp", "bär", "hallon", "blåbär", "jordgubb", "citron", "lime", "fikon", "dadlar")),
    ("Mejeri & Ost", ("ost", "yoghurt", "kvarg", "filmjölk", "gräddfil", "crème fraiche", "creme fraiche", "mjölk", "smör", "bregott", "ägg", "grädde", "keso", "mozzarella", "feta", "brie", "cheddar", "parmesan", "halloumi")),
    ("Bröd & Bageri", ("bröd", "limpa", "fralla", "croissant", "bulle", "bullar", "kaka", "kakor", "tårta", "pepparkak", "lusse", "kex", "knäcke", "tortilla", "pita", "baguette", "muffins", "munk", "donut", "bakverk", "våffl", "pannkak")),
    ("Fryst & Glass", ("glass", "pizza", "pommes", "fryst", "lasagne", "paj", "nuggets", "fiskpinnar", "färdigrätt", "pytt")),
    ("Snacks & Godis", ("chips", "choklad", "godis", "pralin", "popcorn", "ostbågar", "lakrits", "nötter", "mandel", "cashew", "jordnöt", "snacks", "marabou", "aladdin", "paradis", "julkalender", "skumtomt")),
    ("Dryck", ("läsk", "cola", "pepsi", "fanta", "sprite", "julmust", "glögg", "juice", "vatten", "kaffe", "te ", "tepåsar", "energidryck", "red bull", "monster", "nocco", "cider", "öl", "saft", "smoothie", "dryck")),
    ("Skafferi & Pasta", ("pasta", "spaghetti", "makaron", "ris", "nudlar", "mjöl", "socker", "olja", "sås", "ketchup", "senap", "majonnäs", "krydda", "konserv", "sylt", "marmelad", "müsli", "flingor", "gröt", "soppa", "bönor", "linser", "honung", "nutella")),
    ("Hushåll & Hygien", ("toalettpapper", "hushållspapper", "tvättmedel", "diskmedel", "sköljmedel", "schampo", "balsam", "tvål", "tandkräm", "tandborst", "blöjor", "städ", "servett", "avfallspås", "fryspås", "folie", "bakplåtspapper", "deodorant", "hudkräm", "kattmat", "hundmat")),
    ("Hem & Fritid", ("köksmaskin", "stekpanna", "kastrull", "leksak", "jacka", "tröja", "byxa", "strumpor", "filt", "kudde", "lampa", "ljusslinga", "advents", "julstjärna", "julgran", "julpynt", "verktyg", "väggfäste", "batteri", "blockljus", "värmeljus", "blomma", "julstjärna", "amaryllis", "hyacint")),
)


def guess_general_category(text: str) -> str:
    low = (text or "").lower()
    for cat, kws in GENERAL_CATEGORIES:
        if any(k in low for k in kws):
            return cat
    return "Övrigt"


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

    is_rest = bool(slug and slug in baselines)
    b_info = baselines[slug] if is_rest else {"name": "Övrig kampanj", "category": guess_general_category(full_txt), "unit": "st", "yield_pct": 100.0}
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
        "slug": slug or "",
        "is_restaurant": is_rest,
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

        is_rest = bool(item.get("is_restaurant", bool(slug and slug in baselines)))
        verdict = "🛍️ KAMPANJ" if not is_rest else "⚪ ÖVRIG VARA"
        verdict_code = "OTHER" if not is_rest else "NEUTRAL"
        diff_pct = None
        our_best = None
        canon_unit = item["norm_unit"]
        cat_name = item.get("category") or (b.get("category") if b else "Övrigt") or "Övrigt"

        if b and item["norm_unit"] == b["unit"] and b.get("our_best_price") is not None:
            our_best = float(b["our_best_price"])
            rec_p = float(b.get("record_price") or our_best)
            diff_pct = round((u_net - our_best) / our_best * 100.0, 1) if our_best > 0 else 0.0

            if u_net < our_best * 0.97:
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
                "is_restaurant": is_rest,
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
  *, *::before, *::after {{ box-sizing:border-box; }}
  html, body {{ margin:0; max-width:100%; overflow-x:hidden; font-family: system-ui, -apple-system, sans-serif; background:#f1f5f9; color:#0f172a; padding-bottom:44px; }}
  .top {{ background:#0f172a; color:#fff; padding:12px 16px; position:sticky; top:0; z-index:20; display:flex; justify-content:space-between; align-items:center; gap:8px; }}
  .top h1 {{ margin:0; font-size:18px; }}
  .top p {{ margin:3px 0 0; font-size:12px; color:#94a3b8; }}
  .sg-timer {{ display:inline-block; margin-top:4px; font-size:11px; font-weight:700; padding:2px 8px; border-radius:999px; background:#1e293b; color:#38bdf8; border:1px solid #334155; }}
  .sg-timer.warn {{ background:#78350f; color:#fde68a; border-color:#f59e0b; }}
  .sg-timer.expired {{ background:#7f1d1d; color:#fecaca; border-color:#ef4444; }}
  .lang-bar {{ display:flex; gap:4px; flex-shrink:0; }}
  .lang-btn {{ border:1px solid #334155; background:#1e293b; color:#e2e8f0; border-radius:8px; padding:5px 8px; font-size:12px; font-weight:700; cursor:pointer; }}
  .lang-btn.active {{ background:#0284c7; border-color:#38bdf8; color:#fff; }}
  .goog-te-banner-frame, .skiptranslate, #goog-gt-tt, .goog-te-balloon-frame, .goog-tooltip, .VIpgJd-ZVi9od-ORHb-OEVmcd, .VIpgJd-ZVi9od-aZ2wEe-wOHMyf {{ display:none !important; visibility:hidden !important; }}
  .goog-text-highlight {{ background:transparent !important; box-shadow:none !important; }}
  body {{ top:0 !important; }}
  .wrap {{ padding:12px; max-width:660px; margin:0 auto; width:100%; }}
  .filters {{ display:flex; flex-direction:column; gap:8px; margin-bottom:12px; }}
  .row-flex {{ display:flex; gap:6px; align-items:center; width:100%; min-width:0; }}
  .search-input {{ flex:1; min-width:0; padding:10px 10px; border:1px solid #cbd5e1; border-radius:8px; font-size:15px; background:#fff; }}
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
  .thumb {{ width:96px; height:96px; object-fit:contain; background:#fff; border-radius:8px; border:1px solid #e2e8f0; flex-shrink:0; cursor:zoom-in; }}
  .img-modal {{ display:none; position:fixed; inset:0; background:rgba(15,23,42,0.88); z-index:100; align-items:center; justify-content:center; flex-direction:column; padding:20px; cursor:zoom-out; }}
  .img-modal.open {{ display:flex; }}
  .img-modal img {{ max-width:92vw; max-height:78vh; object-fit:contain; background:#fff; border-radius:12px; padding:8px; box-shadow:0 12px 32px rgba(0,0,0,0.4); }}
  .img-modal-cap {{ color:#fff; font-size:15px; font-weight:700; margin-top:12px; text-align:center; max-width:90vw; }}
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
  .date-row {{ margin-top:5px; }}
  .date-pill {{ display:inline-block; font-size:12px; font-weight:700; padding:3px 9px; border-radius:6px; background:#f1f5f9; color:#334155; border:1px solid #cbd5e1; }}
  .date-pill.warn {{ background:#fef3c7; color:#b45309; border-color:#f59e0b; }}
  .date-pill.urgent {{ background:#fee2e2; color:#dc2626; border-color:#ef4444; }}
  .pick-btn {{ border:2px solid #0284c7; background:#fff; color:#0284c7; border-radius:10px; padding:9px 10px; font-weight:700; font-size:13px; cursor:pointer; width:100%; }}
  .pick-btn.picked {{ background:#16a34a; border-color:#16a34a; color:#fff; }}
  .actions {{ display:flex; flex-direction:column; gap:6px; flex-shrink:0; min-width:86px; }}
  .hist-btn {{ border:1px solid #cbd5e1; background:#f8fafc; color:#334155; border-radius:8px; padding:6px 8px; font-weight:600; font-size:12px; cursor:pointer; width:100%; }}
  .hist-btn.open {{ background:#0f172a; color:#fff; border-color:#0f172a; }}
  .hist-box {{ margin-top:8px; padding:8px 10px; background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; font-size:12px; color:#334155; }}
  .hist-row {{ display:flex; justify-content:space-between; padding:2px 0; border-bottom:1px dashed #e2e8f0; }}
  .hist-row:last-child {{ border-bottom:none; }}
  .addr-wrap {{ position:relative; flex:1; }}
  .addr-list {{ position:absolute; top:100%; left:0; right:0; background:#fff; border:1px solid #cbd5e1; border-radius:10px; box-shadow:0 6px 18px rgba(0,0,0,0.12); z-index:50; max-height:220px; overflow-y:auto; display:none; margin-top:4px; }}
  .addr-list.open {{ display:block; }}
  .addr-item {{ padding:9px 12px; font-size:13px; cursor:pointer; border-bottom:1px solid #f1f5f9; color:#0f172a; }}
  .addr-item:last-child {{ border-bottom:none; }}
  .addr-item:hover {{ background:#f0f9ff; }}
  .shop-btn {{ border:1px solid #16a34a; background:#f0fdf4; color:#15803d; border-radius:10px; padding:10px 12px; font-weight:700; font-size:13px; cursor:pointer; white-space:nowrap; }}
  .shop-btn.active {{ background:#16a34a; color:#fff; }}
  .shop-store {{ font-weight:800; font-size:13px; color:#0f172a; margin:8px 0 4px; padding-bottom:2px; border-bottom:1px solid #e2e8f0; }}
  .shop-row {{ display:flex; justify-content:space-between; align-items:center; gap:8px; padding:4px 0; font-size:13px; }}
  .shop-rm {{ border:none; background:none; color:#94a3b8; font-weight:700; cursor:pointer; font-size:14px; padding:2px 6px; }}
  .shop-rm:hover {{ color:#dc2626; }}
  .qty-ctrl {{ display:flex; align-items:center; justify-content:space-between; border:2px solid #16a34a; border-radius:10px; background:#f0fdf4; overflow:hidden; width:100%; }}
  .qty-btn {{ border:none; background:#16a34a; color:#fff; font-weight:800; font-size:16px; width:28px; height:34px; cursor:pointer; padding:0; }}
  .qty-num {{ font-weight:800; font-size:14px; color:#14532d; min-width:24px; text-align:center; }}
  @media (max-width: 560px) {{
    .card {{ flex-direction:column; gap:10px; padding:14px; }}
    .thumb {{ width:100%; height:180px; padding:6px; border-radius:10px; }}
    .info {{ width:100%; }}
    .title {{ font-size:17px; margin:6px 0 4px; }}
    .sub {{ font-size:13px; }}
    .price-main {{ font-size:20px; }}
    .price-qty, .price-unit, .ref-line {{ font-size:13px; }}
    .actions {{ flex-direction:row; width:100%; min-width:0; }}
    .actions > * {{ flex:1; }}
    .pick-btn {{ padding:11px 12px; font-size:15px; }}
    .qty-btn {{ width:40px; height:42px; font-size:18px; }}
    .qty-num {{ font-size:16px; }}
    .hist-btn {{ padding:10px 12px; font-size:14px; }}
  }}
</style>
</head>
<body>
<div class="top">
  <div>
    <h1>🔥 Veckans Rabattlista</h1>
    <p id="metaLbl">Uppdaterad: —</p>
    <div id="sgTimer" class="sg-timer" style="display:none"></div>
  </div>
  <div class="lang-bar notranslate">
    <button class="lang-btn" id="langSv" onclick="setLang('sv')">🇸🇪 SV</button>
    <button class="lang-btn" id="langZh" onclick="setLang('zh-CN')">🇨🇳 中文</button>
    <button class="lang-btn" id="langHr" onclick="setLang('hr')">🇭🇷 HR</button>
  </div>
</div>
<div id="google_translate_element" style="display:none"></div>

<div class="wrap">
  <div class="filters">
    <div class="row-flex">
      <input id="qInput" class="search-input" type="search" placeholder="Sök vara eller butik..." oninput="renderAll()">
      <button id="btnShop" class="shop-btn" onclick="toggleShopPanel()">🛒 Lista (0)</button>
      <button id="btnFilter" class="cfg-btn active" onclick="toggleFilterPanel()">🎛️ Filter</button>
    </div>

    <div class="chips" id="areaChips" style="padding-bottom:2px"></div>

    <div id="shopPanel" style="display:none">
      <div class="card" style="justify-content:space-between;align-items:center;flex-wrap:wrap;background:#f0fdf4;border-color:#86efac">
        <div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap">
          <button class="mini-btn" style="background:#0f172a;color:#fff;border-color:#0f172a" onclick="toggleShopPanel()">← Tillbaka</button>
          <strong style="font-size:15px">🛒 Min inköpslista</strong>
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button id="btnShopRoute" class="mini-btn" style="background:#dcfce7;border-color:#86efac;color:#14532d" onclick="openShopRoute()">🗺️ Kör rutt</button>
          <button class="mini-btn" onclick="copyShopList()">📤 Kopiera</button>
          <button class="mini-btn" onclick="clearShopList()">🗑️ Rensa</button>
        </div>
      </div>
      <div id="shopBody"></div>
    </div>

    <div id="filterPanel" class="varu-panel" style="display:flex;flex-direction:column;gap:8px">
      <div class="row-flex">
        <select id="originSelect" class="prod-select notranslate" style="flex:1" onchange="onOriginSelect()">
          <option value="Arrendatorsvägen 1, 141 62 Huddinge">📍 Start: Arrendatorsvägen 1, 141 62 Huddinge</option>
          <option value="Ringvägen 123, 116 61 Stockholm">🏠 Start: Ringvägen 123, 116 61 Stockholm</option>
          <option value="__custom__">✏️ Annan startadress...</option>
        </select>
      </div>
      <div id="customOriginRow" class="row-flex" style="display:none">
        <div class="addr-wrap">
          <input id="originInput" class="search-input" style="width:100%;box-sizing:border-box" type="text" placeholder="Skriv valfri adress i Sverige..." autocomplete="off" oninput="onOriginType()">
          <div id="addrSuggest" class="addr-list notranslate"></div>
        </div>
        <button id="btnCalcTimes" class="cfg-btn" onclick="fetchLiveTimes()">🚗 Räkna</button>
      </div>
      <div id="liveTimeStatus" style="font-size:12px;color:#0369a1;display:none"></div>

      <div class="row-flex">
        <select id="prodSelect" class="prod-select" style="flex:1" onchange="onProdSelect()">
          <option value="Alla">Alla valda varor</option>
        </select>
        <button id="btnVaror" class="cfg-btn" onclick="toggleVaruPanel()">⚙️ Välj varor</button>
      </div>

      <div id="varuPanel" class="varu-panel" style="margin-bottom:0">
        <div style="display:flex;justify-content:space-between;align-items:center;gap:6px;flex-wrap:wrap">
          <strong style="font-size:13px">Kryssa i vilka varor du vill se i listan:</strong>
          <div style="display:flex;gap:6px">
            <button class="mini-btn" onclick="setAllHidden(false)">Visa alla</button>
            <button class="mini-btn" onclick="setAllHidden(true)">Avmarkera alla</button>
          </div>
        </div>
        <div id="varuGrid" class="varu-grid"></div>
      </div>

      <div style="display:flex;gap:8px;flex-wrap:wrap">
        <label class="toggle-lbl" style="flex:1">
          <input id="onlyRest" type="checkbox" checked onchange="renderAll()">
          🍽️ För restaurangen
        </label>
        <label class="toggle-lbl" style="flex:1">
          <input id="onlyGreen" type="checkbox" onchange="renderAll()">
          🟢 Slår våra priser
        </label>
      </div>

      <div class="sec-lbl">Kategori</div>
      <div class="chips" id="catChips"></div>

      <div class="sec-lbl">Butik</div>
      <div class="chips" id="storeChips"></div>
    </div>
  </div>
  <div id="dealsContainer"></div>
</div>

<div id="imgModal" class="img-modal" onclick="closeImg()">
  <img id="imgModalEl" src="" alt="">
  <div id="imgModalCap" class="img-modal-cap"></div>
</div>

<script>
const DATA = {json_blob};
let activeCat = 'Alla';
let activeStores = new Set();
let activeProd = 'Alla';
let picked = {{}};
let hiddenProds = {{}};
try {{ picked = JSON.parse(localStorage.getItem('kt_cloud_picked') || '{{}}'); }} catch(e) {{}}
try {{ hiddenProds = JSON.parse(localStorage.getItem('kt_cloud_hidden_prods') || '{{}}'); }} catch(e) {{}}

const BRAND_RE = /\\b(MATRIKET|ARLA(?:\\s+KÖKET)?|VALIO|COCA-COLA|FANTA|SPRITE|PEPSI|LOKA|RAMLÖSA|GARANT|ELDORADO|SCAN|FELIX|FINDUS|GB\\s+GLACE|SIA(?:\\s+GLASS)?|TRIUMF(?:\\s+GLASS)?|POSEIDON|OCEAN\\s+SEA|STJÄRNÄGG|GOD\\s+MORGON|BELLAROM|KRONFÅGEL|GULDFÅGELN|ARVID\\s+NORDQUIST|ZO[EÉ]GAS|GEVALIA|LÖFBERGS|BARILLA|KNORR|SANTA\\s+MARIA|HEINZ|BREGOTT|MARIESTADS|NORRLANDS(?:\\s+GULD)?|PRIPPS(?:\\s+BLÅ)?|GRÄNGES|ROYAL\\s+GREENLAND|FAVORINA|DELUXE|MILBONA|INSELMEER|AROY-D|ICA(?:\\s+BASIC)?|COOP(?:\\s+X-TRA)?|WILLYS|MATDAX|LIDL)\\b/gi;
function wrapBrands(str) {{
  return String(str || '').replace(BRAND_RE, '<span class="notranslate">$1</span>');
}}

function openImg(src, title) {{
  if (!src) return;
  document.getElementById('imgModalEl').src = src;
  document.getElementById('imgModalCap').textContent = title || '';
  document.getElementById('imgModal').classList.add('open');
}}

function closeImg() {{
  document.getElementById('imgModal').classList.remove('open');
}}

document.addEventListener('keydown', (e) => {{ if (e.key === 'Escape') closeImg(); }});

let shopPageOpen = false;
function toggleShopPanel() {{
  shopPageOpen = !shopPageOpen;
  const p = document.getElementById('shopPanel');
  const b = document.getElementById('btnShop');
  const deals = document.getElementById('dealsContainer');
  const filters = document.querySelectorAll('.filters > :not(#shopPanel)');
  p.style.display = shopPageOpen ? 'block' : 'none';
  deals.style.display = shopPageOpen ? 'none' : 'block';
  filters.forEach(el => {{
    if (el.id !== 'shopPanel') el.style.display = shopPageOpen ? 'none' : '';
  }});
  b.classList.toggle('active', shopPageOpen);
  if (shopPageOpen) window.scrollTo(0, 0);
  renderShopList();
}}

function getPickQty(key) {{
  const v = picked[key];
  if (v === true) return 1;
  const n = Number(v || 0);
  return n > 0 ? Math.floor(n) : 0;
}}

function buildCardPriceHtml(c, pQty) {{
  const unitGross = c.unit_price_gross_sek != null ? c.unit_price_gross_sek : (c.unit_price_net_sek * (1 + (c.vat_rate || 6) / 100));
  const fmtKr = (v, dropZero) => {{
    const n = Number(v || 0);
    if (dropZero && Math.abs(n - Math.round(n)) < 0.005) return `${{Math.round(n)}} kr`;
    return `${{n.toFixed(2).replace('.', ',')}} kr`;
  }};
  const fmtQty = (q) => String(Number((q || 1).toFixed(2))).replace('.', ',');
  const qtyVal = Number(c.norm_qty || 1);
  const mult = pQty > 1 ? pQty : 1;
  const dispPrice = c.price_gross_sek * mult;
  const dispQty = qtyVal * mult;
  const samePrice = mult === 1 && Math.abs(qtyVal - 1) < 0.01 && Math.abs(c.price_gross_sek - unitGross) < 0.05;
  return samePrice
    ? `<span class="price-main">${{fmtKr(dispPrice, true)}}/${{c.norm_unit}}</span><span class="price-qty">inkl. moms</span>`
    : `<span class="price-main">${{fmtKr(dispPrice, true)}}</span><span class="price-qty">för ${{fmtQty(dispQty)}} ${{c.norm_unit}}</span><span class="price-unit">${{fmtKr(unitGross, false)}}/${{c.norm_unit}}</span>`;
}}

function buildPickCtrlHtml(key, pQty) {{
  return pQty > 0
    ? `<div class="qty-ctrl notranslate"><button class="qty-btn" onclick="changePickQty('${{key}}', -1)">−</button><span class="qty-num">${{pQty}}</span><button class="qty-btn" onclick="changePickQty('${{key}}', 1)">+</button></div>`
    : `<button class="pick-btn" onclick="changePickQty('${{key}}', 1)">+ Lägg till</button>`;
}}

const SB_URL = 'https://gexlvtootcsqyypvxfsy.supabase.co/rest/v1/shared_shopping_list';
const SB_KEY = 'sb_publishable_MmjmtFAK1jIeVtayakbNFg_nxM4W1T3';
const SB_LIST_ID = 're1e475f9';
let sbSaving = false;
let lastSyncedJson = '';

async function syncFromCloud(initial) {{
  if (sbSaving) return;
  try {{
    const resp = await fetch(`${{SB_URL}}?list_id=eq.${{SB_LIST_ID}}&select=items`, {{
      headers: {{ 'apikey': SB_KEY, 'Authorization': 'Bearer ' + SB_KEY }}
    }});
    if (!resp.ok) return;
    const rows = await resp.json();
    if (!rows || !rows[0] || typeof rows[0].items !== 'object') return;
    const remoteItems = rows[0].items || {{}};
    const remoteJson = JSON.stringify(remoteItems);
    if (remoteJson !== lastSyncedJson) {{
      lastSyncedJson = remoteJson;
      picked = remoteItems;
      try {{ localStorage.setItem('kt_cloud_picked', remoteJson); }} catch(e) {{}}
      if (initial) {{
        renderAll();
      }} else {{
        // Patch visible cards in-place without forcing Google Translate re-render
        (DATA.campaigns || []).forEach(c => {{
          const key = 'c_' + c.id;
          const q = getPickQty(key);
          const actEl = document.getElementById('pick_' + key);
          if (actEl) actEl.innerHTML = buildPickCtrlHtml(key, q);
          const prcEl = document.getElementById('prc_' + key);
          if (prcEl) prcEl.innerHTML = buildCardPriceHtml(c, q);
        }});
        renderShopList();
      }}
    }}
  }} catch(e) {{}}
}}

async function pushPickedToCloud() {{
  sbSaving = true;
  const payload = JSON.stringify(picked);
  lastSyncedJson = payload;
  try {{
    await fetch(`${{SB_URL}}?list_id=eq.${{SB_LIST_ID}}`, {{
      method: 'PATCH',
      headers: {{
        'apikey': SB_KEY,
        'Authorization': 'Bearer ' + SB_KEY,
        'Content-Type': 'application/json',
        'Prefer': 'return=minimal'
      }},
      body: JSON.stringify({{ items: picked, updated_at: new Date().toISOString() }})
    }});
  }} catch(e) {{}}
  sbSaving = false;
}}

function changePickQty(key, delta) {{
  const next = getPickQty(key) + delta;
  if (next <= 0) delete picked[key];
  else picked[key] = next;
  try {{ localStorage.setItem('kt_cloud_picked', JSON.stringify(picked)); }} catch(e) {{}}
  const actEl = document.getElementById('pick_' + key);
  if (actEl) actEl.innerHTML = buildPickCtrlHtml(key, next > 0 ? next : 0);
  const prcEl = document.getElementById('prc_' + key);
  if (prcEl) {{
    const item = (DATA.campaigns || []).find(c => ('c_' + c.id) === key);
    if (item) prcEl.innerHTML = buildCardPriceHtml(item, next > 0 ? next : 0);
  }}
  renderShopList();
  pushPickedToCloud();
}}

function getPickedItems() {{
  return (DATA.campaigns || []).filter(c => getPickQty('c_' + c.id) > 0);
}}

function renderShopList() {{
  const items = getPickedItems();
  const totalUnits = items.reduce((acc, c) => acc + getPickQty('c_' + c.id), 0);
  const grandTotal = items.reduce((acc, c) => acc + getPickQty('c_' + c.id) * Number(c.price_gross_sek || 0), 0);
  const btn = document.getElementById('btnShop');
  btn.textContent = `🛒 Lista (${{totalUnits}})`;
  const body = document.getElementById('shopBody');
  if (!items.length) {{
    body.innerHTML = '<div class="card">Inköpslistan är tom. Klicka på <b>← Tillbaka</b> och tryck <b>+ Lägg till</b> på de klipp du vill handla.</div>';
    return;
  }}
  const byStore = {{}};
  items.forEach(c => {{
    if (!byStore[c.store_name]) byStore[c.store_name] = [];
    byStore[c.store_name].push(c);
  }});
  const fmtS = (v, dropZ) => {{
    const n = Number(v || 0);
    if (dropZ && Math.abs(n - Math.round(n)) < 0.005) return `${{Math.round(n)}} kr`;
    return `${{n.toFixed(2).replace('.', ',')}} kr`;
  }};
  const fmtQ = (q) => String(Number((q || 1).toFixed(2))).replace('.', ',');
  const totalBanner = `<div class="card" style="background:#0f172a;color:#fff;border-color:#0f172a;justify-content:space-between;align-items:center">
    <span style="font-size:14px;font-weight:600">Totalt (${{totalUnits}} st)</span>
    <span style="font-size:20px;font-weight:800;color:#4ade80">${{fmtS(grandTotal, true)}}</span>
  </div>`;
  body.innerHTML = totalBanner + Object.keys(byStore).sort((a, b) => a.localeCompare(b, 'sv')).map(st => {{
    const locs = storeLocs(st);
    const homeAddr = userOrigin || DEFAULT_ORIGIN;
    const locPills = locs.map(l => {{
      const cleanD = l.replace(/\\s*\\([^)]*\\)/g, '').trim();
      const qDest = st + (cleanD ? ' ' + cleanD : '');
      const uDir = `https://www.google.com/maps/dir/?api=1&origin=${{encodeURIComponent(homeAddr)}}&destination=${{encodeURIComponent(qDest)}}`;
      return `<a class="loc-tag notranslate" href="${{uDir}}" target="_blank" rel="noopener">📍 ${{l}}</a>`;
    }}).join('');
    const storeSum = byStore[st].reduce((acc, c) => acc + getPickQty('c_' + c.id) * Number(c.price_gross_sek || 0), 0);
    const cardsHtml = byStore[st].map(c => {{
      const key = 'c_' + c.id;
      const q = getPickQty(key);
      const lineSum = q * Number(c.price_gross_sek || 0);
      const imgHtml = c.image_url ? `<img class="thumb" src="${{c.image_url}}" loading="lazy" alt="${{(c.heading || '').replace(/"/g, '&quot;')}}" onclick="openImg(this.src, this.alt)">` : '';
      const unitGross = c.unit_price_gross_sek != null ? c.unit_price_gross_sek : (c.unit_price_net_sek * (1 + (c.vat_rate || 6) / 100));
      const qtyVal = Number(c.norm_qty || 1);
      const sameP = Math.abs(qtyVal - 1) < 0.01 && Math.abs(c.price_gross_sek - unitGross) < 0.05;
      const totalQtyVal = qtyVal * q;
      const pHtml = q > 1
        ? `<span class="price-main">${{fmtS(lineSum, true)}}</span><span class="price-qty">för ${{fmtQ(totalQtyVal)}} ${{c.norm_unit}}</span><span class="price-unit">${{fmtS(unitGross, false)}}/${{c.norm_unit}}</span>`
        : (sameP
            ? `<span class="price-main">${{fmtS(c.price_gross_sek, true)}}/${{c.norm_unit}}</span>`
            : `<span class="price-main">${{fmtS(c.price_gross_sek, true)}}</span><span class="price-qty">för ${{fmtQ(qtyVal)}} ${{c.norm_unit}}</span><span class="price-unit">${{fmtS(unitGross, false)}}/${{c.norm_unit}}</span>`);
      const lim = c.max_limit_note ? ` • ⚠️ ${{c.max_limit_note}}` : '';
      return `<div class="card green">
        ${{imgHtml}}
        <div class="info">
          <div class="title" style="margin-top:0">${{wrapBrands(c.heading)}}</div>
          <div class="sub">${{c.canonical_name}}${{lim}}</div>
          <div class="price-line">${{pHtml}}</div>
        </div>
        <div class="actions">
          <div class="qty-ctrl">
            <button class="qty-btn" onclick="changePickQty('${{key}}', -1)">−</button>
            <span class="qty-num">${{q}}</span>
            <button class="qty-btn" onclick="changePickQty('${{key}}', 1)">+</button>
          </div>
        </div>
      </div>`;
    }}).join('');
    return `<div class="shop-store" style="margin-top:12px;font-size:15px"><span class="notranslate">🏪 ${{st}}</span> • ${{fmtS(storeSum, true)}} ${{locPills}}</div>${{cardsHtml}}`;
  }}).join('');
}}

function openShopRoute() {{
  const items = getPickedItems();
  const stores = Array.from(new Set(items.map(c => c.store_name)));
  if (!stores.length) {{ alert('Lägg till minst en vara i listan först!'); return; }}
  const origin = userOrigin || DEFAULT_ORIGIN;
  const stops = stores.map(st => {{
    const locs = storeLocs(st);
    const first = locs.length ? locs[0].replace(/\\s*\\([^)]*\\)/g, '').trim() : '';
    return st + (first ? ' ' + first : '');
  }});
  const url = `https://www.google.com/maps/dir/?api=1&origin=${{encodeURIComponent(origin)}}&waypoints=${{encodeURIComponent(stops.join('|'))}}&destination=${{encodeURIComponent(origin)}}`;
  window.open(url, '_blank', 'noopener');
}}

function copyShopList() {{
  const items = getPickedItems();
  if (!items.length) {{ alert('Inköpslistan är tom.'); return; }}
  const byStore = {{}};
  items.forEach(c => {{
    if (!byStore[c.store_name]) byStore[c.store_name] = [];
    byStore[c.store_name].push(c);
  }});
  const fmtS = (v) => Math.abs(v - Math.round(v)) < 0.005 ? `${{Math.round(v)}} kr` : `${{Number(v).toFixed(2).replace('.', ',')}} kr`;
  const grandTotal = items.reduce((acc, c) => acc + getPickQty('c_' + c.id) * Number(c.price_gross_sek || 0), 0);
  const lines = [`🛒 Inköpslista (Totalt: ${{fmtS(grandTotal)}}):`];
  Object.keys(byStore).sort((a, b) => a.localeCompare(b, 'sv')).forEach(st => {{
    const sSum = byStore[st].reduce((acc, c) => acc + getPickQty('c_' + c.id) * Number(c.price_gross_sek || 0), 0);
    lines.push('\\n' + st + ` (${{fmtS(sSum)}}):`);
    byStore[st].forEach(c => {{
      const q = getPickQty('c_' + c.id);
      const lSum = q * Number(c.price_gross_sek || 0);
      lines.push(`- ${{q}}x ${{c.heading}} (${{fmtS(lSum)}})`);
    }});
  }});
  const txt = lines.join('\\n');
  if (navigator.clipboard && navigator.clipboard.writeText) {{
    navigator.clipboard.writeText(txt).then(() => alert('Inköpslistan kopierad!'));
  }} else {{
    prompt('Kopiera listan:', txt);
  }}
}}

function clearShopList() {{
  if (!Object.keys(picked).some(k => picked[k])) return;
  picked = {{}};
  try {{ localStorage.setItem('kt_cloud_picked', JSON.stringify(picked)); }} catch(e) {{}}
  renderAll();
  pushPickedToCloud();
}}

function toggleFilterPanel() {{
  const p = document.getElementById('filterPanel');
  const b = document.getElementById('btnFilter');
  const open = p.style.display === 'flex';
  p.style.display = open ? 'none' : 'flex';
  b.classList.toggle('active', !open);
}}

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
  "ICA Supermarket": ["Huddinge (2 min)", "Ringen, Skanstull (20 min)"],
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
const SKANSTULL_STORES = new Set(["ICA Supermarket", "Hemköp"]);
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
let activeArea = 'all';
const DEFAULT_ORIGIN = 'Arrendatorsvägen 1, 141 62 Huddinge';
const SKANSTULL_ORIGIN = 'Ringvägen 123, 116 61 Stockholm';
const PRESET_ORIGINS = new Set([DEFAULT_ORIGIN, SKANSTULL_ORIGIN]);
let userOrigin = DEFAULT_ORIGIN;
try {{ userOrigin = localStorage.getItem('kt_cloud_origin') || DEFAULT_ORIGIN; }} catch(e) {{}}
if (PRESET_ORIGINS.has(userOrigin)) {{
  document.getElementById('originSelect').value = userOrigin;
}} else {{
  document.getElementById('originSelect').value = '__custom__';
  document.getElementById('customOriginRow').style.display = 'flex';
  document.getElementById('originInput').value = userOrigin;
}}

const PRESET_COORDS = {{
  'Arrendatorsvägen 1, 141 62 Huddinge': [17.9819, 59.2367],
  'Ringvägen 123, 116 61 Stockholm': [18.0762, 59.3082]
}};

function onOriginSelect() {{
  const val = document.getElementById('originSelect').value;
  const row = document.getElementById('customOriginRow');
  if (val === '__custom__') {{
    row.style.display = 'flex';
    document.getElementById('originInput').focus();
    userOrigin = (document.getElementById('originInput').value || '').trim() || DEFAULT_ORIGIN;
    renderAll();
  }} else {{
    row.style.display = 'none';
    userOrigin = val;
    try {{ localStorage.setItem('kt_cloud_origin', userOrigin); }} catch(e) {{}}
    const pc = PRESET_COORDS[val];
    if (pc && !liveTimesCache[val]) {{
      fetchLiveTimes(pc[0], pc[1], val);
    }} else {{
      renderAll();
    }}
  }}
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
  "Hemköp": ["Skanstull (1 min)", "Huddinge (17 min)"],
  "ICA Kvantum": ["Skanstull (1 min)", "Farsta (9 min)"],
  "ICA Maxi Stormarknad": ["Haninge (17 min)", "Flemingsberg (20 min)"],
  "ICA Nära": ["Segeltorp (11 min)", "Huddinge (12 min)"],
  "ICA Supermarket": ["Ringen, Skanstull (1 min)", "Huddinge (15 min)"],
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

let addrTimer = null;
function onOriginType() {{
  onOriginChange();
  const q = (document.getElementById('originInput').value || '').trim();
  const box = document.getElementById('addrSuggest');
  if (addrTimer) clearTimeout(addrTimer);
  if (q.length < 3) {{ box.classList.remove('open'); box.innerHTML = ''; return; }}
  addrTimer = setTimeout(async () => {{
    try {{
      const u = `https://nominatim.openstreetmap.org/search?format=json&countrycodes=se&addressdetails=1&limit=6&q=${{encodeURIComponent(q)}}`;
      const resp = await fetch(u, {{ headers: {{ 'Accept-Language': 'sv' }} }});
      const feats = await resp.json();
      if (!feats || !feats.length) {{ box.classList.remove('open'); return; }}
      box.innerHTML = '';
      feats.forEach(f => {{
        const a = f.address || {{}};
        const road = a.road || a.pedestrian || a.footway || '';
        const hnr = a.house_number ? ` ${{a.house_number}}` : '';
        const city = a.city || a.town || a.village || a.municipality || a.suburb || '';
        const parts = [road ? (road + hnr) : (f.display_name || '').split(',')[0], a.postcode, city].filter(Boolean);
        const lbl = parts.join(', ');
        if (!lbl) return;
        const div = document.createElement('div');
        div.className = 'addr-item';
        div.textContent = '📍 ' + lbl;
        div.onclick = () => {{
          document.getElementById('originInput').value = lbl;
          box.classList.remove('open');
          userOrigin = lbl;
          try {{ localStorage.setItem('kt_cloud_origin', userOrigin); }} catch(e) {{}}
          fetchLiveTimes(Number(f.lon), Number(f.lat));
        }};
        box.appendChild(div);
      }});
      box.classList.add('open');
    }} catch(e) {{
      box.classList.remove('open');
    }}
  }}, 300);
}}

document.addEventListener('click', (e) => {{
  const box = document.getElementById('addrSuggest');
  if (box && !e.target.closest('.addr-wrap')) box.classList.remove('open');
}});

let liveTimesCache = {{}};
try {{ liveTimesCache = JSON.parse(localStorage.getItem('kt_live_times') || '{{}}'); }} catch(e) {{}}

const PLACE_COORDS = {{
  "Huddinge": [17.9819, 59.2367],
  "Stuvsta": [17.9970, 59.2500],
  "Rågsved": [18.0278, 59.2564],
  "Högdalen": [18.0422, 59.2633],
  "Hökarängen": [18.0825, 59.2578],
  "Flemingsberg": [17.9465, 59.2195],
  "Länna": [18.1460, 59.1930],
  "Kungens Kurva": [17.9175, 59.2705],
  "Skärholmen": [17.9070, 59.2772],
  "Alby": [17.8450, 59.2395],
  "Farsta": [18.0933, 59.2430],
  "Skanstull": [18.0762, 59.3082],
  "Haninge": [18.1360, 59.1680],
  "Segeltorp": [17.9475, 59.2770],
  "Västberga": [18.0040, 59.2935],
  "Vårby": [17.8820, 59.2635],
  "Älvsjö": [18.0105, 59.2785],
  "Arninge, Täby": [18.1355, 59.4570]
}};

async function fetchLiveTimes(oLonArg, oLatArg, addrOverride) {{
  const addr = (addrOverride || document.getElementById('originInput').value || '').trim();
  if (!addr) {{ alert('Skriv in en startadress först.'); return; }}
  const stEl = document.getElementById('liveTimeStatus');
  const btn = document.getElementById('btnCalcTimes');
  stEl.style.display = 'block';
  stEl.textContent = `⏳ Räknar körtider från ${{addr}}...`;
  btn.disabled = true;

  try {{
    let oLon = oLonArg, oLat = oLatArg;
    if (typeof oLon !== 'number' || typeof oLat !== 'number' || isNaN(oLon) || isNaN(oLat)) {{
      const gResp = await fetch(`https://nominatim.openstreetmap.org/search?format=json&countrycodes=se&limit=1&q=${{encodeURIComponent(addr)}}`, {{ headers: {{ 'Accept-Language': 'sv' }} }});
      const gData = await gResp.json();
      if (!gData || !gData[0]) throw new Error('Hittade inte adressen');
      oLon = Number(gData[0].lon);
      oLat = Number(gData[0].lat);
    }}
    const placeNames = Object.keys(PLACE_COORDS);
    const coordsStr = [`${{oLon}},${{oLat}}`, ...placeNames.map(p => `${{PLACE_COORDS[p][0]}},${{PLACE_COORDS[p][1]}}`)].join(';');
    const osrmUrl = `https://router.project-osrm.org/table/v1/driving/${{coordsStr}}?sources=0&annotations=duration`;
    const oResp = await fetch(osrmUrl);
    if (!oResp.ok) throw new Error('HTTP ' + oResp.status);
    const oData = await oResp.json();
    const durs = (oData.durations && oData.durations[0]) || [];
    const placeMins = {{}};
    placeNames.forEach((p, idx) => {{
      const sec = durs[idx + 1];
      if (typeof sec === 'number' && sec >= 0) placeMins[p] = Math.max(1, Math.round(sec / 60));
    }});

    const resMap = {{}};
    Object.keys(STORE_LOCATIONS).forEach(st => {{
      const basePlaces = (STORE_LOCATIONS[st] || []).map(l => l.replace(/\\s*\\([^)]*\\)/g, '').trim());
      resMap[st] = basePlaces.map(p => (placeMins[p] != null ? `${{p}} (${{placeMins[p]}} min)` : p));
    }});

    liveTimesCache[addr] = resMap;
    try {{ localStorage.setItem('kt_live_times', JSON.stringify(liveTimesCache)); }} catch(e) {{}}
    userOrigin = addr;
    try {{ localStorage.setItem('kt_cloud_origin', userOrigin); }} catch(e) {{}}
    stEl.textContent = `✅ Körtider uppdaterade från ${{addr}}`;
  }} catch(e) {{
    stEl.textContent = `⚠️ Kunde inte räkna tider (${{e.message || e}})`;
  }}
  btn.disabled = false;
  renderAll();
}}

function storeLocs(name) {{
  const keyOrigin = activeArea === 'skanstull' ? SKANSTULL_ORIGIN : userOrigin;
  if (liveTimesCache[keyOrigin] && liveTimesCache[keyOrigin][name]) return liveTimesCache[keyOrigin][name];
  if (activeArea === 'skanstull' || userOrigin === SKANSTULL_ORIGIN) return STORE_LOCATIONS_SKANSTULL[name] || [];
  if (userOrigin === DEFAULT_ORIGIN) return STORE_LOCATIONS[name] || [];
  return (STORE_LOCATIONS[name] || []).map(l => l.replace(/\\s*\\([^)]*\\)/g, '').trim());
}}

function storeLoc(name) {{
  return storeLocs(name).join(' ');
}}

function renderAll() {{
  renderShopList();
  const areaBox = document.getElementById('areaChips');
  const areaOpts = [
    ['all', '🗺️ Alla butiker'],
    ['near', '📍 Nära Arrendatorsvägen'],
    ['skanstull', '🏠 I Skanstull'],
    ['route', '🚗 Skanstull → Jobbet']
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
  const onlyR = document.getElementById('onlyRest').checked;
  const onlyG = document.getElementById('onlyGreen').checked;

  const visibleBase = (DATA.campaigns || []).filter(c => {{
    if (onlyR && !c.is_restaurant) return false;
    if (hiddenProds[c.canonical_name]) return false;
    if (onlyG && c.verdict_code !== 'GREEN') return false;
    if (activeArea === 'near' && FAR_STORES.has(c.store_name)) return false;
    if (activeArea === 'skanstull' && !SKANSTULL_STORES.has(c.store_name)) return false;
    if (activeArea === 'route' && !ROUTE_STORES.has(c.store_name)) return false;
    const loc = storeLoc(c.store_name).toLowerCase();
    if (q && !(c.heading.toLowerCase().includes(q) || c.canonical_name.toLowerCase().includes(q) || (c.category || '').toLowerCase().includes(q) || c.store_name.toLowerCase().includes(q) || loc.includes(q))) return false;
    return true;
  }});

  const forCatCounts = activeStores.size === 0 ? visibleBase : visibleBase.filter(c => activeStores.has(c.store_name));
  const catCounts = {{}};
  forCatCounts.forEach(c => {{
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
    b.textContent = ct === 'Alla' ? `Alla (${{forCatCounts.length}})` : `${{ct}} (${{catCounts[ct]}})`;
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
  Array.from(activeStores).forEach(s => {{ if (!stCounts[s]) activeStores.delete(s); }});
  const stores = ['Alla', ...Object.keys(stCounts).sort((a, b) => stCounts[b] - stCounts[a])];
  const chipBox = document.getElementById('storeChips');
  chipBox.innerHTML = '';
  stores.forEach(st => {{
    const b = document.createElement('button');
    const isAct = st === 'Alla' ? activeStores.size === 0 : activeStores.has(st);
    b.className = 'chip' + (isAct ? ' active' : '') + (st === 'Alla' ? '' : ' notranslate');
    const locs = storeLocs(st);
    const firstLoc = locs.length ? locs[0].trim() : '';
    const mTime = firstLoc.match(/\\(([^)]+)\\)/);
    const timePrefix = mTime ? `${{mTime[1]}} · ` : '';
    const shortLoc = firstLoc.replace(/\\s*\\([^)]*\\)/g, '').trim();
    b.textContent = st === 'Alla' ? `Alla butiker (${{afterProd.length}})` : `${{timePrefix}}${{st}}${{shortLoc ? ' · ' + shortLoc : ''}} (${{stCounts[st]}})`;
    b.onclick = () => {{
      if (st === 'Alla') {{
        activeStores.clear();
      }} else {{
        if (activeStores.has(st)) activeStores.delete(st);
        else activeStores.add(st);
      }}
      renderAll();
    }};
    chipBox.appendChild(b);
  }});

  const rows = activeStores.size === 0 ? afterProd : afterProd.filter(c => activeStores.has(c.store_name));
  const fBtn = document.getElementById('btnFilter');
  const fCnt = (activeCat !== 'Alla' ? 1 : 0) + activeStores.size + (activeProd !== 'Alla' ? 1 : 0) + (!onlyG ? 1 : 0);
  if (fBtn) fBtn.textContent = fCnt > 0 ? `🎛️ Filter (${{fCnt}})` : '🎛️ Filter';
  const hiddenCnt = Object.keys(hiddenProds).length;
  const hiddenNote = hiddenCnt > 0 ? ` • ${{hiddenCnt}} bortfiltrerade varor` : '';
  document.getElementById('metaLbl').textContent =
    `Uppdaterad: ${{DATA.generated_at || ''}} • ${{rows.length}} rabatterade klipp${{hiddenNote}}`;

  const cont = document.getElementById('dealsContainer');
  if (!rows.length) {{
    cont.innerHTML = '<div class="card">Inga rabatter matchar filtret just nu. Justera varu-/kategorifiltret eller avmarkera rutan ovan för att visa alla priser.</div>';
    return;
  }}

  const displayRows = rows.slice(0, 250);
  const moreNote = rows.length > 250 ? `<div class="card" style="justify-content:center;color:#475569;font-size:13px">Visar 250 av ${{rows.length}} kampanjer — sök eller välj butik/kategori för att se fler.</div>` : '';
  cont.innerHTML = displayRows.map(c => {{
    const key = 'c_' + c.id;
    const pQty = getPickQty(key);
    const isP = pQty > 0;
    const cls = c.verdict_code === 'GREEN' ? 'green' : (c.verdict_code === 'YELLOW' ? 'yellow' : '');
    const imgHtml = c.image_url ? `<img class="thumb" src="${{c.image_url}}" loading="lazy" alt="${{(c.heading || '').replace(/"/g, '&quot;')}}" onclick="openImg(this.src, this.alt)">` : '';
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
    const priceBlockHtml = buildCardPriceHtml(c, pQty);
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
      return `<a class="loc-tag notranslate" href="${{uDir}}" target="_blank" rel="noopener">📍 ${{l}}</a>`;
    }}).join('');
    const firstClean = locs.length ? locs[0].replace(/\\s*\\([^)]*\\)/g, '').trim() : '';
    const firstQuery = c.store_name + (firstClean ? ' ' + firstClean : '');
    const hemvagUrl = locs.length ? `https://www.google.com/maps/dir/?api=1&origin=${{encodeURIComponent(SKANSTULL_ORIGIN)}}&waypoints=${{encodeURIComponent(firstQuery)}}&destination=${{encodeURIComponent(DEFAULT_ORIGIN)}}` : '';
    const rtTime = ROUTE_TIMES[c.store_name] ? ` (${{ROUTE_TIMES[c.store_name]}})` : '';
    const locHtml = locs.length ? `${{locPills}}<a class="route-tag" href="${{hemvagUrl}}" target="_blank" rel="noopener" title="Skanstull → ${{c.store_name}} → Arrendatorsvägen">🚗 Till jobbet${{rtTime}}</a>` : '';
    let validPill = `<span class="date-pill">📅 T.o.m. ${{c.valid_until || 'söndag'}}</span>`;
    if (c.valid_until && /^\\d{{4}}-\\d{{2}}-\\d{{2}}$/.test(c.valid_until)) {{
      const td = new Date(); td.setHours(0, 0, 0, 0);
      const ex = new Date(c.valid_until + 'T00:00:00');
      const dl = Math.round((ex - td) / 86400000);
      const daysSv = ['sön', 'mån', 'tis', 'ons', 'tor', 'fre', 'lör'];
      const dStr = `${{daysSv[ex.getDay()]}} ${{ex.getDate()}}/${{ex.getMonth() + 1}}`;
      if (dl <= 0) validPill = `<span class="date-pill urgent">⏰ Sista dagen idag (${{dStr}})!</span>`;
      else if (dl === 1) validPill = `<span class="date-pill urgent">⏰ Går ut imorgon (${{dStr}})</span>`;
      else if (dl === 2) validPill = `<span class="date-pill warn">⏳ T.o.m. ${{dStr}} (2 dagar kvar)</span>`;
      else validPill = `<span class="date-pill">📅 T.o.m. ${{dStr}}</span>`;
    }}
    return `<div class="card ${{cls}} ${{isP ? 'done' : ''}}">
      ${{imgHtml}}
      <div class="info">
        <div><span class="store-tag notranslate">${{c.store_name}}</span>${{locHtml}}<span class="cat-tag">${{c.category || 'Basvara'}}</span><span class="save-tag">${{c.verdict}}${{savePct}}</span></div>
        <div class="title">${{wrapBrands(c.heading)}}</div>
        ${{descShort ? `<div class="sub" style="color:#334155">${{wrapBrands(descShort)}}</div>` : ''}}
        <div class="sub">${{c.canonical_name}}${{lim}}</div>
        <div class="price-line" id="prc_${{key}}">${{priceBlockHtml}}</div>
        <div class="ref-line">${{ourTxt}}</div>
        <div class="date-row">${{validPill}}</div>
        ${{histHtml}}
      </div>
      <div class="actions">
        <div id="pick_${{key}}">${{buildPickCtrlHtml(key, pQty)}}</div>
        ${{histBtnHtml}}
      </div>
    </div>`;
  }}).join('') + moreNote;
}}

function setLang(lang) {{
  if (lang === 'sv') {{
    document.cookie = 'googtrans=; path=/; expires=Thu, 01 Jan 1970 00:00:00 GMT';
    document.cookie = 'googtrans=; path=/; domain=' + location.hostname + '; expires=Thu, 01 Jan 1970 00:00:00 GMT';
  }} else {{
    document.cookie = 'googtrans=/sv/' + lang + '; path=/';
    document.cookie = 'googtrans=/sv/' + lang + '; path=/; domain=' + location.hostname;
  }}
  try {{ localStorage.setItem('kt_cloud_lang', lang); }} catch(e) {{}}
  location.reload();
}}

function googleTranslateElementInit() {{
  new google.translate.TranslateElement({{
    pageLanguage: 'sv',
    includedLanguages: 'zh-CN,hr',
    autoDisplay: false
  }}, 'google_translate_element');
}}

(function() {{
  let curLang = 'sv';
  try {{ curLang = localStorage.getItem('kt_cloud_lang') || 'sv'; }} catch(e) {{}}
  const map = {{ 'sv': 'langSv', 'zh-CN': 'langZh', 'hr': 'langHr' }};
  const el = document.getElementById(map[curLang] || 'langSv');
  if (el) el.classList.add('active');
  if (curLang !== 'sv') {{
    document.cookie = 'googtrans=/sv/' + curLang + '; path=/';
  }}
}})();

function renderSgTimer() {{
  const el = document.getElementById('sgTimer');
  if (!el) return;
  const sgDates = (DATA.campaigns || [])
    .filter(c => (c.store_name || '').toLowerCase().includes('snabbgross') && c.valid_until)
    .map(c => c.valid_until)
    .sort();
  if (!sgDates.length) {{
    el.style.display = 'inline-block';
    el.className = 'sg-timer expired';
    el.textContent = '🔴 Snabbgross-kampanj saknas/utgången – lägg in ny!';
    return;
  }}
  const latest = sgDates[sgDates.length - 1];
  const today = new Date();
  today.setHours(0, 0, 0, 0);
  const exp = new Date(latest + 'T00:00:00');
  const diffDays = Math.round((exp - today) / 86400000);
  el.style.display = 'inline-block';
  if (diffDays < 0) {{
    el.className = 'sg-timer expired';
    el.textContent = `🔴 Snabbgross gick ut ${{latest}} – lägg in ny kampanj!`;
  }} else if (diffDays === 0) {{
    el.className = 'sg-timer warn';
    el.textContent = `⚠️ Snabbgross: Sista dagen idag (${{latest}}) – lägg in ny imorgon!`;
  }} else if (diffDays <= 2) {{
    el.className = 'sg-timer warn';
    el.textContent = `⏳ Snabbgross: ${{diffDays}} ${{diffDays === 1 ? 'dag' : 'dagar'}} kvar (t.o.m. ${{latest}})`;
  }} else {{
    el.className = 'sg-timer';
    el.textContent = `⏳ Snabbgross: ${{diffDays}} dagar kvar (t.o.m. ${{latest}})`;
  }}
}}

buildVaruCheckboxes();
renderSgTimer();
renderAll();
if (PRESET_COORDS[userOrigin] && !liveTimesCache[userOrigin]) {{
  fetchLiveTimes(PRESET_COORDS[userOrigin][0], PRESET_COORDS[userOrigin][1], userOrigin);
}}
syncFromCloud(true);
setInterval(() => {{ if (!document.hidden) syncFromCloud(false); }}, 5000);
</script>
<script src="https://translate.google.com/translate_a/element.js?cb=googleTranslateElementInit"></script>
</body>
</html>"""


def build_b2b_html(payload: Dict[str, Any]) -> str:
    json_blob = json.dumps(payload, ensure_ascii=False).replace("</", "<\\/")
    return f"""<!doctype html>
<html lang="sv">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex,nofollow">
<title>B2B Förråd & Inventering – Grossistpriser</title>
<style>
  body {{ margin:0; font-family: system-ui, -apple-system, sans-serif; background:#f1f5f9; color:#0f172a; padding-bottom:56px; top:0 !important; }}
  .goog-te-banner-frame.skiptranslate, .goog-te-gadget-icon, #goog-gt-tt, .VIpgJd-ZVi9od-ORHb-OEVmcd {{ display:none !important; }}
  .top {{ background:#0f172a; color:#fff; padding:12px 16px; position:sticky; top:0; z-index:30; display:flex; justify-content:space-between; align-items:center; gap:10px; }}
  .top h1 {{ margin:0; font-size:17px; }}
  .top p {{ margin:3px 0 0; font-size:12px; color:#94a3b8; }}
  .lang-bar {{ display:flex; gap:4px; flex-shrink:0; }}
  .lang-btn {{ border:1px solid #334155; background:#1e293b; color:#e2e8f0; border-radius:6px; padding:5px 7px; font-size:12px; font-weight:700; cursor:pointer; }}
  .lang-btn.active {{ background:#0284c7; border-color:#38bdf8; color:#fff; }}
  .wrap {{ padding:12px; max-width:740px; margin:0 auto; }}
  .inv-bar {{ background:#fff; border:2px solid #0284c7; border-radius:12px; padding:11px 13px; margin-bottom:12px; box-shadow:0 2px 8px rgba(15,23,42,0.06); }}
  .inv-top {{ display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:8px; }}
  .inv-tot-main {{ font-size:17px; font-weight:800; color:#0f172a; }}
  .inv-tot-sub {{ font-size:12px; color:#475569; font-weight:600; margin-top:2px; }}
  .inv-period {{ display:flex; align-items:center; flex-wrap:wrap; gap:6px 10px; margin-bottom:10px; font-size:13px; font-weight:700; }}
  .inv-period input {{ font:inherit; color:inherit; background:#fff; border:1px solid #94a3b8; border-radius:8px; padding:6px 8px; }}
  .inv-save-status {{ color:#475569; font-size:12px; font-weight:600; }}
  .inv-save-status.error {{ color:#b91c1c; }}
  .inv-btns {{ display:flex; gap:6px; flex-wrap:wrap; margin-top:9px; }}
  .mini-btn {{ border:1px solid #cbd5e1; background:#f8fafc; color:#0f172a; border-radius:8px; padding:7px 10px; font-size:12.5px; font-weight:700; cursor:pointer; }}
  .mini-btn.primary {{ background:#0284c7; border-color:#0284c7; color:#fff; }}
  .mini-btn.green {{ background:#16a34a; border-color:#16a34a; color:#fff; }}
  .mini-btn.danger {{ background:#fef2f2; border-color:#fecaca; color:#b91c1c; }}
  .filters {{ display:flex; flex-direction:column; gap:8px; margin-bottom:12px; }}
  .search {{ width:100%; box-sizing:border-box; padding:10px 12px; border:1px solid #cbd5e1; border-radius:8px; font-size:15px; background:#fff; }}
  .sec-lbl {{ font-size:11px; font-weight:700; color:#475569; text-transform:uppercase; letter-spacing:0.4px; margin-top:2px; }}
  .chips {{ display:flex; flex-wrap:wrap; gap:6px; padding-bottom:4px; }}
  .chip {{ border:1px solid #cbd5e1; background:#fff; border-radius:999px; padding:6px 12px; font-size:13px; font-weight:700; white-space:nowrap; cursor:pointer; color:#1e293b; }}
  .chip.active {{ background:#ea580c; color:#fff; border-color:#ea580c; }}
  .chip.cat-chip.active {{ background:#0284c7; color:#fff; border-color:#0284c7; }}
  .card {{ background:#fff; border-radius:12px; padding:12px; margin-bottom:10px; border:1px solid #cbd5e1; display:flex; justify-content:space-between; gap:12px; align-items:flex-start; }}
  .card.multi {{ border-left:5px solid #0284c7; }}
  .card.counted {{ border:2px solid #16a34a; border-left:6px solid #16a34a; background:#f0fdf4; }}
  .info {{ flex:1; min-width:0; }}
  .sup-tag {{ display:inline-block; background:#0f172a; color:#fff; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; }}
  .cat-tag {{ display:inline-block; background:#e0f2fe; color:#0369a1; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; margin-right:4px; }}
  .multi-tag {{ display:inline-block; background:#dcfce7; color:#14532d; font-size:11px; font-weight:700; padding:2px 7px; border-radius:5px; }}
  .title {{ font-weight:800; font-size:15px; margin:5px 0 4px; color:#0f172a; }}
  .sup-list {{ display:flex; flex-direction:column; gap:3px; margin:4px 0; }}
  .sup-row {{ display:flex; justify-content:space-between; align-items:center; gap:8px; font-size:12.5px; background:#f8fafc; padding:5px 8px; border-radius:6px; border:1px solid #e2e8f0; cursor:pointer; }}
  .sup-row.chosen {{ background:#eff6ff; border-color:#3b82f6; color:#1e3a8a; font-weight:700; }}
  .sup-row.best {{ border-color:#86efac; }}
  .sub {{ font-size:12px; color:#475569; margin-top:3px; }}
  .inv-ctrl {{ display:flex; align-items:center; gap:6px; margin-top:8px; flex-wrap:wrap; }}
  .inv-lbl {{ font-size:12.5px; font-weight:700; color:#0f172a; }}
  .step-btn {{ width:34px; height:36px; border:1px solid #cbd5e1; background:#fff; border-radius:8px; font-size:18px; font-weight:800; cursor:pointer; color:#0f172a; line-height:1; }}
  .qty-inp {{ width:76px; height:36px; box-sizing:border-box; border:1.5px solid #94a3b8; border-radius:8px; text-align:center; font-size:15px; font-weight:800; background:#fff; color:#0f172a; }}
  .qty-inp:focus {{ outline:none; border-color:#0284c7; box-shadow:0 0 0 2px rgba(2,132,199,0.2); }}
  .unit-pill {{ font-size:13px; font-weight:800; color:#334155; }}
  .b2b-tabs {{ display:flex; gap:6px; margin-bottom:10px; }}
  .b2b-tab {{ flex:1; border:1px solid #cbd5e1; background:#fff; color:#334155; border-radius:10px; padding:10px 12px; font-size:13.5px; font-weight:800; cursor:pointer; text-align:center; }}
  .b2b-tab.active {{ background:#0f172a; color:#fff; border-color:#0f172a; }}
  .cat-sum-grid {{ display:flex; flex-wrap:wrap; gap:6px; margin-top:8px; padding-top:8px; border-top:1px dashed #e2e8f0; }}
  .cat-pill {{ border:1px solid #cbd5e1; background:#f8fafc; border-radius:8px; padding:5px 9px; font-size:12px; cursor:pointer; color:#1e293b; display:flex; gap:6px; align-items:center; }}
  .cat-pill.active {{ background:#0284c7; color:#fff; border-color:#0284c7; }}
  .spend-bar-bg {{ height:6px; background:#e2e8f0; border-radius:999px; overflow:hidden; margin-top:7px; }}
  .spend-bar-fill {{ height:100%; background:#0284c7; border-radius:999px; }}
  .rank-badge {{ display:inline-block; background:#0f172a; color:#fff; font-size:11px; font-weight:800; padding:2px 7px; border-radius:6px; margin-right:5px; }}
  .unit-toggle {{ border:1px solid #cbd5e1; background:#f1f5f9; color:#0f172a; border-radius:8px; padding:6px 9px; font-size:12.5px; font-weight:800; cursor:pointer; white-space:nowrap; }}
  .unit-toggle:hover {{ background:#e2e8f0; border-color:#94a3b8; }}
  .pack-sub {{ font-size:11.5px; font-weight:700; color:#475569; }}
  .line-val {{ font-size:13px; font-weight:800; color:#15803d; background:#dcfce7; padding:4px 8px; border-radius:6px; display:none; }}
  .line-val.show {{ display:inline-block; }}
  .actions {{ display:flex; flex-direction:column; align-items:flex-end; gap:6px; flex-shrink:0; min-width:108px; }}
  .p-main {{ font-size:15px; font-weight:800; color:#0f172a; text-align:right; }}
  .p-avg {{ font-size:11px; color:#64748b; text-align:right; }}
  .hist-btn {{ border:1px solid #cbd5e1; background:#f8fafc; color:#334155; border-radius:8px; padding:6px 9px; font-weight:600; font-size:12px; cursor:pointer; width:100%; }}
  .hist-btn.open {{ background:#0f172a; color:#fff; border-color:#0f172a; }}
  .hist-box {{ margin-top:8px; padding:8px 10px; background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; font-size:12px; color:#334155; }}
  .hist-row {{ display:flex; justify-content:space-between; align-items:flex-start; gap:8px; padding:6px 6px; border-bottom:1px dashed #e2e8f0; border-radius:6px; cursor:pointer; transition:background 0.12s; }}
  .hist-row:hover {{ background:#e0f2fe; }}
  .hist-row:last-child {{ border-bottom:none; }}
  .hist-art {{ font-size:11px; color:#64748b; }}
  .inv-link-pill {{ display:inline-block; font-size:10.5px; font-weight:700; color:#0284c7; background:#e0f2fe; padding:1px 6px; border-radius:4px; margin-left:4px; }}
  .doc-overlay {{ position:fixed; inset:0; background:rgba(15,23,42,0.65); z-index:100; display:none; align-items:center; justify-content:center; padding:12px; }}
  .doc-overlay.open {{ display:flex; }}
  .doc-dialog {{ background:#fff; border-radius:14px; max-width:860px; width:100%; max-height:88vh; display:flex; flex-direction:column; overflow:hidden; box-shadow:0 12px 32px rgba(0,0,0,0.28); }}
  .doc-head {{ background:#0f172a; color:#fff; padding:12px 15px; display:flex; justify-content:space-between; align-items:flex-start; gap:10px; }}
  .doc-head h3 {{ margin:0; font-size:16px; }}
  .doc-head p {{ margin:3px 0 0; font-size:12px; color:#cbd5e1; }}
  .doc-head-btns {{ display:flex; gap:6px; align-items:center; flex-shrink:0; flex-wrap:wrap; }}
  .doc-pdf-btn {{ display:inline-block; text-decoration:none; background:#16a34a; color:#fff; border-radius:8px; padding:6px 11px; font-size:12.5px; font-weight:800; white-space:nowrap; }}
  .doc-pdf-btn:hover {{ background:#15803d; }}
  .doc-close {{ border:none; background:#334155; color:#fff; border-radius:8px; padding:6px 11px; font-size:13px; font-weight:800; cursor:pointer; }}
  .doc-body {{ padding:0; overflow:auto; flex:1; }}
  .doc-tbl {{ width:100%; border-collapse:collapse; font-size:12.5px; }}
  .doc-tbl th {{ position:sticky; top:0; background:#f1f5f9; color:#334155; font-size:11px; text-transform:uppercase; letter-spacing:0.3px; padding:8px 10px; border-bottom:1.5px solid #cbd5e1; text-align:left; white-space:nowrap; z-index:2; }}
  .doc-tbl th.num, .doc-tbl td.num {{ text-align:right; white-space:nowrap; }}
  .doc-tbl th.cnt, .doc-tbl td.cnt {{ text-align:center; white-space:nowrap; }}
  .doc-tbl td {{ padding:7px 10px; border-bottom:1px solid #f1f5f9; vertical-align:top; }}
  .doc-tbl tr.hl td {{ background:#fef9c3; font-weight:700; border-top:1.5px solid #facc15; border-bottom:1.5px solid #facc15; }}
  .doc-col-short {{ display:none; }}
  .doc-foot {{ background:#f8fafc; border-top:1px solid #cbd5e1; padding:10px 15px; font-size:13px; display:flex; justify-content:space-between; flex-wrap:wrap; gap:8px; }}
  .modal-box {{ background:#fff; border:1px solid #cbd5e1; border-radius:12px; padding:12px; margin-bottom:12px; display:none; }}
  .modal-box.open {{ display:block; }}
  .form-row {{ display:flex; gap:6px; flex-wrap:wrap; margin-top:8px; }}
  .form-inp {{ flex:1; min-width:110px; padding:8px 10px; border:1px solid #cbd5e1; border-radius:8px; font-size:14px; }}
  @media (max-width: 680px) {{
    .wrap {{ padding:9px; }}
    .top > div:first-child {{ min-width:0; overflow-wrap:anywhere; }}
    .card {{ padding:10px; gap:8px; }}
    .card .info {{ overflow-wrap:anywhere; }}
    .actions {{ min-width:84px; max-width:34%; }}
    .p-main {{ font-size:13px; }}
    .hist-btn {{ padding:6px; }}
    .chips {{ gap:4px; }}
    .chip {{ max-width:100%; padding:4px 7px; font-size:11.5px; white-space:normal; overflow-wrap:anywhere; }}
    .search, .qty-inp, .form-inp, .inv-period input {{ font-size:16px; }}
    .form-inp {{ box-sizing:border-box; max-width:100%; }}
    .doc-overlay {{ padding:6px; }}
    .doc-dialog {{ max-height:calc(100dvh - 16px); }}
    .doc-head {{ flex-wrap:wrap; gap:8px; padding:9px 10px; }}
    .doc-head-btns {{ flex-shrink:1; }}
    .doc-tbl {{ table-layout:fixed; font-size:11px; }}
    .doc-tbl th, .doc-tbl td {{ padding:5px 3px; overflow-wrap:anywhere; }}
    .doc-tbl th {{ font-size:10px; text-transform:none; letter-spacing:0; }}
    .doc-tbl th, .doc-tbl .num, .doc-tbl .cnt {{ white-space:normal; }}
    .doc-tbl th:nth-child(1) {{ width:25%; }}
    .doc-tbl th:nth-child(2) {{ width:12%; }}
    .doc-tbl th:nth-child(3), .doc-tbl th:nth-child(6) {{ width:8%; }}
    .doc-tbl th:nth-child(4), .doc-tbl th:nth-child(5) {{ width:15%; }}
    .doc-tbl th:nth-child(7) {{ width:17%; }}
    .doc-tbl th {{ box-sizing:border-box; }}
    .doc-col-long, .doc-currency {{ display:none; }}
    .doc-col-short {{ display:inline; }}
    .doc-price-unit {{ display:block; font-size:10px; }}
    .doc-foot {{ font-size:12px; padding:9px 12px; }}
  }}
</style>
</head>
<body>
<div class="top">
  <div>
    <h1>📦 Förråd & B2B Inventering</h1>
    <p id="metaLbl">Laddar...</p>
  </div>
  <div class="lang-bar notranslate">
    <button class="lang-btn" id="langSv" onclick="setLang('sv')">🇸🇪 SV</button>
    <button class="lang-btn" id="langZh" onclick="setLang('zh-CN')">🇨🇳 中文</button>
    <button class="lang-btn" id="langHr" onclick="setLang('hr')">🇭🇷 HR</button>
  </div>
</div>
<div id="google_translate_element" style="display:none"></div>

<div class="wrap">
  <div class="b2b-tabs notranslate">
    <button id="tabInvBtn" class="b2b-tab active" onclick="switchB2bTab('inv')">📦 Förråd & Inventering</button>
    <button id="tabSpendBtn" class="b2b-tab" onclick="switchB2bTab('spend')">📊 Ackumulerade Inköp & Priser</button>
  </div>

  <div id="viewInv">
  <div class="inv-bar">
    <div class="inv-period">
      <label for="invMonth">Inventeringsmånad</label>
      <input id="invMonth" type="month" placeholder="ÅÅÅÅ-MM" pattern="[0-9]{{4}}-(0[1-9]|1[0-2])" onchange="changeInventoryMonth(this)">
      <span id="invSaveStatus" class="inv-save-status" role="status"></span>
    </div>
    <div class="inv-top">
      <div>
        <div class="inv-tot-main" id="invTotMain">📦 Förrådsvärde: 0,00 kr</div>
        <div class="inv-tot-sub" id="invTotSub">0 inventerade varor • Skriv in mängd (kg / L / st) nedan</div>
      </div>
      <button id="btnVatMode" class="mini-btn" onclick="toggleVatMode()">Visar: Exkl. moms</button>
    </div>
    <div class="inv-btns">
      <button id="btnOnlyStock" class="mini-btn primary" onclick="toggleOnlyStock()">📦 Visa förrådslista (0)</button>
      <button class="mini-btn green" onclick="copyInventoryReport()">📤 Kopiera rapport</button>
      <button class="mini-btn" onclick="exportInventoryCsv()">📥 Excel (CSV)</button>
      <button class="mini-btn" onclick="toggleCustomForm()">➕ Egen vara</button>
      <button class="mini-btn danger" onclick="clearInventory()">🗑️ Nollställ</button>
    </div>
  </div>

  <div id="customForm" class="modal-box">
    <strong style="font-size:14px">➕ Lägg till egen vara i förrådet</strong>
    <div class="form-row">
      <input id="cName" class="form-inp" type="text" placeholder="Varunamn (t.ex. Lax fryst)">
      <input id="cQty" class="form-inp" style="max-width:90px" type="number" step="any" placeholder="Mängd">
      <select id="cUnit" class="form-inp" style="max-width:95px">
        <option value="kg">kg</option>
        <option value="L">L</option>
        <option value="st">st</option>
        <option value="säck">säck</option>
        <option value="burk">burk</option>
        <option value="flaska">flaska</option>
        <option value="dunk">dunk</option>
        <option value="påse">påse</option>
        <option value="låda">låda</option>
        <option value="förp">förp</option>
      </select>
      <input id="cPrice" class="form-inp" style="max-width:120px" type="number" step="any" placeholder="À-pris exkl. moms">
      <button class="mini-btn green" onclick="addCustomItem()">Spara</button>
    </div>
  </div>

  <div class="filters" id="filterArea">
    <div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">
      <input id="qInput" class="search" style="flex:1;min-width:180px" type="search" placeholder="Sök vara, artikel, kategori eller grossist..." oninput="renderB2B()">
      <select id="b2bSort" class="form-inp" style="max-width:210px;height:40px;font-weight:700" onchange="setSortMode(this.value)">
        <option value="kop">Sortera: Flest köp</option>
        <option value="spend_desc">💰 Högsta ack. inköp (kr)</option>
        <option value="name">Sortera: Namn (A–Ö)</option>
      </select>
    </div>
    <div class="sec-lbl">Kategori</div>
    <div class="chips" id="catChips"></div>
    <div class="sec-lbl">Grossister</div>
    <div class="chips" id="supChips" role="group" aria-label="Grossistfilter"></div>
  </div>

  <div id="listBox"></div>
  </div>

  <div id="viewSpend" style="display:none">
    <div class="inv-bar">
      <div class="inv-top">
        <div>
          <div class="inv-tot-main notranslate" id="spSumMain">0,00 kr</div>
          <div class="inv-tot-sub" id="spSumSub">Beräknar...</div>
        </div>
        <button id="btnSpVat" class="mini-btn" onclick="toggleVatMode()">Visar: Exkl. moms</button>
      </div>
      <div class="cat-sum-grid" id="spCatGrid"></div>
    </div>
    <div class="filters">
      <div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">
        <input id="spQInput" class="search" style="flex:1;min-width:180px" type="search" placeholder="Sök vara, kategori eller grossist..." oninput="renderSpend()">
        <select id="spSortSel" class="form-inp" style="max-width:210px;height:40px;font-weight:700" onchange="spSortMode=this.value;renderSpend()">
          <option value="kr_desc">💰 Högsta ack. pris (kr)</option>
          <option value="qty_desc">📦 Största mängd</option>
          <option value="kop_desc">🔢 Flest köp</option>
          <option value="name_asc">🔤 Namn (A–Ö)</option>
        </select>
      </div>
      <div class="sec-lbl">Månad</div>
      <div class="chips" id="spMonthChips"></div>
      <div class="sec-lbl">Kategori</div>
      <div class="chips" id="spCatChips"></div>
      <div class="sec-lbl">Grossister (välj en eller flera)</div>
      <div class="chips" id="spSupChips"></div>
    </div>
    <div id="spListBox"></div>
  </div>
</div>

<div id="docOverlay" class="doc-overlay" onclick="if(event.target===this)closeInvoiceModal()">
  <div class="doc-dialog">
    <div class="doc-head">
      <div>
        <h3 id="docTitle">Faktura</h3>
        <p id="docSub"></p>
      </div>
      <div class="doc-head-btns">
        <button id="docVatBtn" class="doc-close" style="background:#0284c7" onclick="toggleDocVat()">💰 Exkl. moms</button>
        <a id="docPdfBtn" class="doc-pdf-btn" href="#" target="_blank" rel="noopener" style="display:none">📑 Öppna PDF ↗</a>
        <button class="doc-close" onclick="closeInvoiceModal()">✕ Stäng</button>
      </div>
    </div>
    <div id="docBody" class="doc-body"></div>
    <div id="docFoot" class="doc-foot"></div>
  </div>
</div>
<script>
const B2B = {json_blob};
let activeCat = 'Alla';
const activeSuppliers = new Set();
let openHist = {{}};
let onlyStock = false;
let showInclVat = false;

const inventoryPrefix = 'kt_b2b_inventory:';
const currentMonth = new Intl.DateTimeFormat('sv-SE', {{
  year: 'numeric', month: '2-digit', timeZone: 'Europe/Stockholm'
}}).format(new Date());
const monthPattern = /^[0-9]{{4}}-(0[1-9]|1[0-2])$/;
const requestedMonth = new URLSearchParams(location.search).get('month') || '';
let inventoryMonth = monthPattern.test(requestedMonth) ? requestedMonth : currentMonth;
let invQty = {{}};
let invUnitMode = {{}};
let histShowAck = {{}};
let histSups = {{}};
let histMonth = {{}};
let chosenSup = {{}};
let sortMode = 'kop';
let customItems = [];
let inventoryItems = {{}};
try {{
  const savedVat = localStorage.getItem('kt_b2b_vat_v2');
  if (savedVat !== null) showInclVat = savedVat === '1';
}} catch(e) {{}}

function esc(s) {{
  return String(s || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}}

function fmtSv(n) {{
  const r = Math.round((Number(n || 0) + 1e-9) * 100) / 100;
  return r.toLocaleString('sv-SE', {{ minimumFractionDigits: 2, maximumFractionDigits: 2 }});
}}

function catalogItems() {{
  return [...customItems, ...(B2B.items || [])];
}}

function allItems() {{
  const items = catalogItems();
  const ids = new Set(items.map(x => x.id));
  return [...items, ...Object.values(inventoryItems).filter(x => !ids.has(x.id))];
}}

function getUnitPrices(x) {{
  return inventoryItems[x.id]?.prices || getCatalogPrices(x);
}}

function visibleSuppliers(x) {{
  const sups = x.suppliers || [];
  return activeSuppliers.size ? sups.filter(s => activeSuppliers.has(s.grossist)) : sups;
}}

function getCatalogPrices(x, sups = x.suppliers || []) {{
  let sObj = null;
  if (chosenSup[x.id]) sObj = sups.find(s => s.grossist === chosenSup[x.id]);
  if (!sObj && x.latest_supplier) sObj = sups.find(s => s.grossist === x.latest_supplier);
  if (!sObj && sups.length) sObj = sups[0];
  const gross = sObj ? Number(sObj.latest_gross) : Number(x.latest_gross || x.best_gross || 0);
  const net = sObj ? Number(sObj.latest_net) : Number(x.latest_net || x.best_net || (gross / 1.06));
  const avgG = sObj ? Number(sObj.avg_gross) : Number(x.avg_gross || gross);
  const avgN = sObj ? Number(sObj.avg_net) : Number(x.avg_net || net);
  const supName = sObj ? sObj.grossist : (x.latest_supplier || 'Egen vara');
  return {{ gross, net, avgG, avgN, supName }};
}}

function hasPack(x) {{
  return Boolean(x && Number(x.pack_qty) > 0 && x.pack_unit);
}}

function isPackMode(x) {{
  return hasPack(x) && invUnitMode[x.id] !== 'base';
}}

function getDisplayQty(x, baseQty) {{
  const q = Number(baseQty || 0);
  if (!isPackMode(x)) return q;
  return Math.round((q / Number(x.pack_qty)) * 1000) / 1000;
}}

function toBaseQty(x, displayQty) {{
  const q = Number(displayQty || 0);
  if (!isPackMode(x)) return Math.round(q * 1000) / 1000;
  return Math.round((q * Number(x.pack_qty)) * 10000) / 10000;
}}

function fmtQtySv(n) {{
  const r = Math.round((Number(n || 0) + 1e-9) * 1000) / 1000;
  return String(r).replace('.', ',');
}}

function captureInventoryItem(x) {{
  const visible = visibleSuppliers(x);
  const prices = visible.length ? getCatalogPrices(x, visible) : getCatalogPrices(x);
  inventoryItems[x.id] = {{
    id: x.id, vara: x.vara, category: x.category, unit: x.unit,
    pack_qty: x.pack_qty || null, pack_unit: x.pack_unit || null,
    latest_supplier: prices.supName, latest_date: x.latest_date, prices,
    suppliers: [{{ grossist: prices.supName, latest_net: prices.net, latest_gross: prices.gross }}]
  }};
}}

function inventoryStatus(message, error = false) {{
  const el = document.getElementById('invSaveStatus');
  el.textContent = message;
  el.classList.toggle('error', error);
}}

function loadInventory() {{
  const saved = JSON.parse(localStorage.getItem(inventoryPrefix + inventoryMonth));
  ({{ invQty = {{}}, invUnitMode = {{}}, chosenSup = {{}}, customItems = [], inventoryItems = {{}} }} = saved || {{}});
  return saved;
}}

function migrateInventory() {{
  const marker = inventoryPrefix + 'migrated';
  if (localStorage.getItem(marker)) return;
  if (!localStorage.getItem(inventoryPrefix + currentMonth)) {{
    invQty = JSON.parse(localStorage.getItem('kt_b2b_inv_qty')) || {{}};
    chosenSup = JSON.parse(localStorage.getItem('kt_b2b_chosen_sup')) || {{}};
    customItems = JSON.parse(localStorage.getItem('kt_b2b_custom_items')) || [];
    catalogItems().forEach(x => {{ if (invQty[x.id] > 0) captureInventoryItem(x); }});
    if (Object.keys(invQty).length || Object.keys(chosenSup).length || customItems.length) saveInventory(currentMonth);
  }}
  localStorage.setItem(marker, '1');
}}

function showInventoryMonth() {{
  document.getElementById('invMonth').value = inventoryMonth;
  invQty = {{}};
  invUnitMode = {{}};
  chosenSup = {{}};
  customItems = [];
  inventoryItems = {{}};
  try {{
    const saved = loadInventory();
    inventoryStatus(saved ? 'Sparat i den här webbläsaren' : 'Sparas automatiskt i den här webbläsaren');
  }} catch(e) {{
    inventoryStatus('Kunde inte läsa inventeringen i den här webbläsaren.', true);
  }}
  renderB2B();
  updateSummaryBar();
}}

function changeInventoryMonth(input) {{
  if (!monthPattern.test(input.value)) {{
    input.value = inventoryMonth;
    return;
  }}
  inventoryMonth = input.value;
  const url = new URL(location.href);
  url.searchParams.set('month', inventoryMonth);
  history.replaceState(null, '', url);
  showInventoryMonth();
}}

function saveInventory(month) {{
  localStorage.setItem(inventoryPrefix + month, JSON.stringify({{ invQty, invUnitMode, chosenSup, customItems, inventoryItems }}));
}}

function saveInv() {{
  try {{
    saveInventory(inventoryMonth);
    inventoryStatus('Sparat i den här webbläsaren');
  }} catch(e) {{
    inventoryStatus('Kunde inte spara inventeringen i den här webbläsaren.', true);
  }}
  updateSummaryBar();
}}

function setInventoryQty(id, quantity) {{
  if (quantity > 0) {{
    invQty[id] = quantity;
    if (!inventoryItems[id]) {{
      const item = catalogItems().find(x => x.id === id);
      if (item) captureInventoryItem(item);
    }}
  }} else {{
    delete invQty[id];
    delete inventoryItems[id];
  }}
}}

function updateSummaryBar() {{
  let cnt = 0;
  let totGross = 0;
  let totNet = 0;
  allItems().forEach(x => {{
    const q = Number(invQty[x.id] || 0);
    if (q > 0) {{
      cnt += 1;
      const p = getUnitPrices(x);
      totGross += q * p.gross;
      totNet += q * p.net;
    }}
  }});
  const mainVal = showInclVat ? totGross : totNet;
  const otherVal = showInclVat ? totNet : totGross;
  const mainLbl = showInclVat ? 'inkl. moms' : 'exkl. moms';
  const otherLbl = showInclVat ? 'exkl. moms' : 'inkl. moms';
  document.getElementById('invTotMain').textContent = `📦 Förrådsvärde: ${{fmtSv(mainVal)}} kr (${{mainLbl}})`;
  document.getElementById('invTotSub').textContent =
    `${{cnt}} varor i förrådet • ${{fmtSv(otherVal)}} kr ${{otherLbl}}`;
  const btnStock = document.getElementById('btnOnlyStock');
  btnStock.textContent = onlyStock ? `← Visa alla varor` : `📦 Visa förrådslista (${{cnt}})`;
  document.getElementById('btnVatMode').textContent = showInclVat ? 'Visar: Inkl. moms' : 'Visar: Exkl. moms';
}}

function onQtyInput(id, rawVal) {{
  const x = allItems().find(it => it.id === id);
  const cleaned = String(rawVal || '').replace(',', '.');
  const v = parseFloat(cleaned);
  const baseV = Number.isFinite(v) && v > 0 ? toBaseQty(x, v) : 0;
  setInventoryQty(id, baseV);
  saveInv();
  updateCardInPlace(id);
}}

function stepQty(id, delta) {{
  const x = allItems().find(it => it.id === id);
  const curBase = Number(invQty[id] || 0);
  const curDisp = getDisplayQty(x, curBase);
  const nextDisp = Math.max(0, Math.round((curDisp + delta) * 1000) / 1000);
  const nextBase = nextDisp > 0 ? toBaseQty(x, nextDisp) : 0;
  setInventoryQty(id, nextBase);
  const inp = document.getElementById('qinp_' + id);
  if (inp) inp.value = nextDisp > 0 ? String(nextDisp) : '';
  saveInv();
  updateCardInPlace(id);
  if (onlyStock && nextBase === 0) renderB2B();
}}

function toggleUnitMode(id) {{
  const x = allItems().find(it => it.id === id);
  if (!hasPack(x)) return;
  invUnitMode[id] = isPackMode(x) ? 'base' : 'pack';
  saveInv();
  renderB2B();
}}

function toggleHistAck(id) {{
  histShowAck[id] = !histShowAck[id];
  renderB2B();
}}

function toggleHistSup(id, supName) {{
  const x = allItems().find(it => it.id === id);
  if (!x) return;
  const allSups = [...new Set((x.history || []).map(h => h.supplier).concat((x.suppliers || []).map(s => s.grossist)))];
  let cur = histSups[id] ? new Set(histSups[id]) : new Set(activeSuppliers.size ? [...activeSuppliers].filter(s => allSups.includes(s)) : allSups);
  if (cur.has(supName)) {{
    if (cur.size > 1) cur.delete(supName);
  }} else {{
    cur.add(supName);
  }}
  histSups[id] = [...cur];
  renderB2B();
}}

function toggleHistMonth(id, ym) {{
  histMonth[id] = (histMonth[id] === ym || !ym) ? '' : ym;
  renderB2B();
}}

function updateCardInPlace(id) {{
  const x = allItems().find(it => it.id === id);
  if (!x) return;
  const q = Number(invQty[id] || 0);
  const p = getUnitPrices(x);
  const uPrice = showInclVat ? p.gross : p.net;
  const cardEl = document.getElementById('card_' + id);
  if (cardEl) cardEl.classList.toggle('counted', q > 0);
  const peqEl = document.getElementById('peq_' + id);
  if (peqEl && hasPack(x)) {{
    if (q > 0) {{
      if (isPackMode(x)) {{
        peqEl.textContent = `= ${{fmtQtySv(q)}} ${{x.unit}}`;
      }} else {{
        const packs = Math.round((q / Number(x.pack_qty)) * 100) / 100;
        peqEl.textContent = `= ${{fmtQtySv(packs)}} ${{x.pack_unit}}`;
      }}
    }} else {{
      peqEl.textContent = '';
    }}
  }}
  const lvEl = document.getElementById('lval_' + id);
  if (lvEl) {{
    if (q > 0) {{
      lvEl.textContent = `= ${{fmtSv(q * uPrice)}} kr`;
      lvEl.classList.add('show');
    }} else {{
      lvEl.textContent = '';
      lvEl.classList.remove('show');
    }}
  }}
}}

function selectSupForVara(id, supName) {{
  chosenSup[id] = supName;
  const item = inventoryItems[id] && catalogItems().find(x => x.id === id);
  if (item) captureInventoryItem(item);
  saveInv();
  renderB2B();
}}

function toggleVatMode() {{
  showInclVat = !showInclVat;
  try {{ localStorage.setItem('kt_b2b_vat_v2', showInclVat ? '1' : '0'); }} catch(e) {{}}
  updateSummaryBar();
  renderB2B();
  if (curB2bTab === 'spend') renderSpend();
}}

function toggleOnlyStock() {{
  onlyStock = !onlyStock;
  updateSummaryBar();
  renderB2B();
}}

function toggleCustomForm() {{
  document.getElementById('customForm').classList.toggle('open');
}}

function addCustomItem() {{
  const name = (document.getElementById('cName').value || '').trim();
  const q = parseFloat(String(document.getElementById('cQty').value || '0').replace(',', '.'));
  const u = document.getElementById('cUnit').value || 'kg';
  const pNet = parseFloat(String(document.getElementById('cPrice').value || '0').replace(',', '.'));
  if (!name || isNaN(pNet) || pNet <= 0) {{
    alert('Ange både varunamn och à-pris!');
    return;
  }}
  const id = 'cust_' + Date.now();
  const pGross = Math.round((pNet * 1.06) * 100) / 100;
  const today = new Date().toISOString().slice(0, 10);
  const newItem = {{
    id,
    vara: name,
    category: 'Egna varor',
    unit: u,
    vat_rate: 6.0,
    best_net: pNet,
    best_gross: pGross,
    best_supplier: 'Egen inmatning',
    latest_net: pNet,
    latest_gross: pGross,
    latest_date: today,
    latest_supplier: 'Egen inmatning',
    avg_net: pNet,
    avg_gross: pGross,
    kop: 1,
    suppliers: [{{ grossist: 'Egen inmatning', latest_net: pNet, latest_gross: pGross, avg_net: pNet, avg_gross: pGross, kop: 1, datum: today, artikel: name, forp: '' }}],
    history: [{{ date: today, supplier: 'Egen inmatning', artikel: name, forp: '', price_net: pNet, price_gross: pGross, unit: u }}]
  }};
  customItems.unshift(newItem);
  if (Number.isFinite(q) && q > 0) setInventoryQty(id, q);
  document.getElementById('cName').value = '';
  document.getElementById('cQty').value = '';
  document.getElementById('cPrice').value = '';
  document.getElementById('customForm').classList.remove('open');
  saveInv();
  renderB2B();
}}

function deleteCustomItem(id) {{
  customItems = customItems.filter(x => x.id !== id);
  setInventoryQty(id, 0);
  saveInv();
  renderB2B();
}}

function clearInventory() {{
  if (!confirm(`Vill du nollställa förrådsmängderna för ${{inventoryMonth}}?`)) return;
  invQty = {{}};
  inventoryItems = {{}};
  saveInv();
  renderB2B();
}}

function formatQtySummary(x, baseQty) {{
  if (hasPack(x)) {{
    const packs = Math.round((baseQty / Number(x.pack_qty)) * 100) / 100;
    return `${{fmtQtySv(packs)}} ${{x.pack_unit}} (${{fmtQtySv(baseQty)}} ${{x.unit}})`;
  }}
  return `${{fmtQtySv(baseQty)}} ${{x.unit}}`;
}}

function copyInventoryReport() {{
  const counted = allItems().filter(x => Number(invQty[x.id] || 0) > 0);
  if (!counted.length) {{
    alert('Inga varor har mängd > 0 i förrådet ännu.');
    return;
  }}
  let totG = 0, totN = 0;
  const lines = [`📦 LAGERINVENTERING (${{inventoryMonth}})`, '----------------------------------------'];
  counted.forEach(x => {{
    const q = Number(invQty[x.id]);
    const p = getUnitPrices(x);
    const lG = q * p.gross;
    const lN = q * p.net;
    totG += lG;
    totN += lN;
    const uP = showInclVat ? p.gross : p.net;
    const lV = showInclVat ? lG : lN;
    lines.push(`• ${{x.vara}}: ${{formatQtySummary(x, q)}} × ${{fmtSv(uP)}} kr/${{x.unit}} = ${{fmtSv(lV)}} kr (${{p.supName}})`);
  }});
  lines.push('----------------------------------------');
  lines.push(`Totalt EXKL. moms: ${{fmtSv(totN)}} kr`);
  lines.push(`Totalt INKL. moms: ${{fmtSv(totG)}} kr`);
  const txt = lines.join('\\n');
  if (navigator.clipboard && navigator.clipboard.writeText) {{
    navigator.clipboard.writeText(txt).then(() => alert('Inventeringsrapport kopierad!')).catch(() => prompt('Kopiera texten:', txt));
  }} else {{
    prompt('Kopiera texten:', txt);
  }}
}}

function exportInventoryCsv() {{
  const counted = allItems().filter(x => Number(invQty[x.id] || 0) > 0);
  if (!counted.length) {{
    alert('Inga varor har mängd > 0 i förrådet ännu.');
    return;
  }}
  const rows = [['Vara', 'Kategori', 'Grossist', 'Antal förp', 'Förpackning', 'Mängd', 'Enhet', 'À-pris exkl moms', 'À-pris inkl moms', 'Värde exkl moms', 'Värde inkl moms']];
  let totG = 0, totN = 0;
  counted.forEach(x => {{
    const q = Number(invQty[x.id]);
    const p = getUnitPrices(x);
    const lN = q * p.net;
    const lG = q * p.gross;
    totN += lN;
    totG += lG;
    const packCnt = hasPack(x) ? String(Math.round((q / Number(x.pack_qty)) * 100) / 100).replace('.', ',') : '';
    const packLbl = hasPack(x) ? `${{x.pack_unit}} (${{fmtQtySv(x.pack_qty)}} ${{x.unit}})` : '';
    rows.push([
      x.vara, x.category || '', p.supName,
      packCnt, packLbl,
      String(q).replace('.', ','), x.unit,
      p.net.toFixed(2).replace('.', ','), p.gross.toFixed(2).replace('.', ','),
      lN.toFixed(2).replace('.', ','), lG.toFixed(2).replace('.', ',')
    ]);
  }});
  rows.push(['TOTALT', '', '', '', '', '', '', '', '', totN.toFixed(2).replace('.', ','), totG.toFixed(2).replace('.', ',')]);
  const csv = '\\uFEFF' + rows.map(r => r.map(c => `"${{String(c).replace(/"/g, '""')}}"`).join(';')).join('\\r\\n');
  const blob = new Blob([csv], {{ type: 'text/csv;charset=utf-8;' }});
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `lagerinventering_${{inventoryMonth}}.csv`;
  a.click();
}}

function toggleHist(id) {{
  openHist[id] = !openHist[id];
  renderB2B();
}}

let curDocId = null;
let curLineId = null;
let docInclVat = false;

function toggleDocVat() {{
  docInclVat = !docInclVat;
  if (curDocId !== null) renderInvoiceModalBody();
}}

function openInvoiceModal(docId, lineId) {{
  const invMap = B2B.invoices || {{}};
  const doc = invMap[String(docId)];
  if (!doc) {{
    alert('Fakturaspecifikation saknas för denna rad.');
    return;
  }}
  curDocId = docId;
  curLineId = lineId;
  document.getElementById('docTitle').textContent = `📄 ${{doc.doc_type}} – ${{doc.supplier}}`;
  document.getElementById('docSub').textContent = `Datum: ${{doc.date}} • ${{doc.lines.length}} varurader`;
  const pdfBtn = document.getElementById('docPdfBtn');
  if (doc.pdf_url) {{
    pdfBtn.href = doc.pdf_url;
    pdfBtn.textContent = doc.pdf_url.endsWith('.pdf') ? '📑 Öppna PDF ↗' : '📑 Öppna kvittobild ↗';
    pdfBtn.style.display = 'inline-block';
  }} else {{
    pdfBtn.style.display = 'none';
  }}
  renderInvoiceModalBody();
  document.getElementById('docOverlay').classList.add('open');
  setTimeout(() => {{
    const hlEl = document.getElementById('dln_' + lineId);
    if (hlEl) hlEl.scrollIntoView({{ block: 'center', inline: 'nearest', behavior: 'smooth' }});
  }}, 60);
}}

function renderInvoiceModalBody() {{
  const invMap = B2B.invoices || {{}};
  const doc = invMap[String(curDocId)];
  if (!doc) return;
  const vLbl = docInclVat ? 'inkl.' : 'exkl.';
  document.getElementById('docVatBtn').textContent = docInclVat ? '💰 Visar: Inkl. moms' : '💰 Visar: Exkl. moms';
  const bodyEl = document.getElementById('docBody');
  const rowsHtml = [];
  doc.lines.forEach(ln => {{
    const isHl = Number(ln.line_id) === Number(curLineId);
    const bQty = ln.qty_billed != null ? ln.qty_billed : 1;
    const bUnit = ln.unit_billed || ln.unit || 'st';
    const bPrice = docInclVat
      ? (ln.billed_gross != null ? ln.billed_gross : ln.unit_gross)
      : (ln.billed_net != null ? ln.billed_net : ln.unit_net);
    const uPrice = docInclVat ? ln.unit_gross : ln.unit_net;
    const tPrice = docInclVat ? ln.total_gross : ln.total_net;
    const vatPct = ln.vat_rate != null ? Number(ln.vat_rate) : 6;
    const qtyFmt = Number(bQty).toLocaleString('sv-SE', {{ maximumFractionDigits: 3 }});
    rowsHtml.push(
      `<tr id="dln_${{ln.line_id}}" class="${{isHl ? 'hl' : ''}}">` +
        `<td><div>${{isHl ? '👉 ' : ''}}${{esc(ln.desc)}}</div>` +
          `<div style="font-size:11px;color:#64748b">${{esc(ln.qty_str)}}${{ln.disc > 0 ? ' • Rabatt: -' + fmtSv(ln.disc) + ' kr' : ''}}</div></td>` +
        `<td class="num notranslate">${{qtyFmt}}</td>` +
        `<td class="cnt notranslate">${{esc(bUnit)}}</td>` +
        `<td class="num notranslate" style="color:#0369a1;font-weight:700">${{fmtSv(uPrice)}}<span class="doc-price-unit"> kr/${{esc(ln.unit)}}</span></td>` +
        `<td class="num notranslate">${{fmtSv(bPrice)}}<span class="doc-currency"> kr</span></td>` +
        `<td class="cnt notranslate">${{vatPct}}%</td>` +
        `<td class="num notranslate" style="font-weight:700">${{fmtSv(tPrice)}}<span class="doc-currency"> kr</span></td>` +
      `</tr>`
    );
  }});
  bodyEl.innerHTML =
    `<table class="doc-tbl">` +
      `<thead><tr><th>Artikel</th><th class="num">Antal</th><th class="cnt">Enhet</th>` +
      `<th class="num"><span class="doc-col-long">Pris/kg (${{vLbl}})</span><span class="doc-col-short">Jfr-pris</span></th>` +
      `<th class="num"><span class="doc-col-long">Enhetspris (${{vLbl}})</span><span class="doc-col-short">À-pris</span></th>` +
      `<th class="cnt">Moms</th><th class="num"><span class="doc-col-long">Belopp (${{vLbl}})</span><span class="doc-col-short">Belopp</span></th></tr></thead>` +
      `<tbody>${{rowsHtml.join('')}}</tbody></table>`;
  document.getElementById('docFoot').innerHTML =
    `<span>Netto (exkl. moms): <b class="notranslate">${{fmtSv(doc.net_total)}} kr</b></span>` +
    `<span>Moms: <b class="notranslate">${{fmtSv(doc.vat_total)}} kr</b></span>` +
    `<span>Totalt (inkl. moms): <b class="notranslate">${{fmtSv(doc.gross_total)}} kr</b></span>`;
}}

function closeInvoiceModal() {{
  document.getElementById('docOverlay').classList.remove('open');
}}
document.addEventListener('keydown', e => {{ if (e.key === 'Escape') closeInvoiceModal(); }});

function matchesQuery(x, q) {{
  if (!q) return true;
  if ((x.vara || '').toLowerCase().includes(q)) return true;
  if ((x.category || '').toLowerCase().includes(q)) return true;
  if ((x.suppliers || []).some(s => s.grossist.toLowerCase().includes(q) || (s.artikel || '').toLowerCase().includes(q))) return true;
  if ((x.history || []).some(h => (h.artikel || '').toLowerCase().includes(q))) return true;
  return false;
}}

function setSortMode(mode) {{
  sortMode = mode || 'kop';
  renderB2B();
}}

function accumulatedSpend(x, supFilter) {{
  if (!supFilter || !supFilter.size) {{
    if (showInclVat && Number(x.total_gross) > 0) return Number(x.total_gross);
    if (!showInclVat && Number(x.total_net) > 0) return Number(x.total_net);
  }}
  let tot = 0;
  (x.history || []).forEach(h => {{
    if (supFilter && supFilter.size && !supFilter.has(h.supplier)) return;
    const hp = showInclVat ? h.price_gross : h.price_net;
    const lTot = showInclVat ? (h.line_gross ?? (Number(h.qty || 0) * hp)) : (h.line_net ?? (Number(h.qty || 0) * hp));
    tot += Number(lTot || 0);
  }});
  return Math.round(tot * 100) / 100;
}}

function purchaseCount(item, suppliers) {{
  const history = item.history || [];
  if (!suppliers.size) return item.kop ?? history.length;
  let total = 0;
  for (const supplier of suppliers) {{
    const info = (item.suppliers || []).find(s => s.grossist === supplier);
    total += info?.kop ?? history.filter(h => h.supplier === supplier).length;
  }}
  return total;
}}

function renderB2B() {{
  const q = (document.getElementById('qInput').value || '').toLowerCase().trim();
  const base = allItems().filter(x => {{
    if (onlyStock && !(Number(invQty[x.id] || 0) > 0)) return false;
    return matchesQuery(x, q);
  }});

  const catCounts = {{}};
  base.forEach(x => {{
    const c = x.category || 'Övrigt';
    catCounts[c] = (catCounts[c] || 0) + 1;
  }});
  if (activeCat !== 'Alla' && !catCounts[activeCat]) activeCat = 'Alla';
  const cats = ['Alla', ...Object.keys(catCounts).sort((a, b) => catCounts[b] - catCounts[a])];
  const catBox = document.getElementById('catChips');
  catBox.innerHTML = '';
  cats.forEach(c => {{
    const b = document.createElement('button');
    b.className = 'chip cat-chip' + (c === activeCat ? ' active' : '');
    b.textContent = c === 'Alla' ? `Alla (${{base.length}})` : `${{c}} (${{catCounts[c]}})`;
    b.onclick = () => {{ activeCat = c; renderB2B(); }};
    catBox.appendChild(b);
  }});

  const afterCat = activeCat === 'Alla' ? base : base.filter(x => (x.category || 'Övrigt') === activeCat);

  const supCounts = {{}};
  afterCat.forEach(x => {{
    (x.suppliers || []).forEach(s => {{
      supCounts[s.grossist] = (supCounts[s.grossist] || 0) + 1;
    }});
  }});
  for (const supplier of activeSuppliers) supCounts[supplier] ??= 0;
  const sups = ['Alla', ...Object.keys(supCounts).sort((a, b) => supCounts[b] - supCounts[a])];
  const chipBox = document.getElementById('supChips');
  chipBox.innerHTML = '';
  sups.forEach(s => {{
    const b = document.createElement('button');
    const selected = s === 'Alla' ? !activeSuppliers.size : activeSuppliers.has(s);
    b.className = 'chip' + (selected ? ' active' : '');
    b.setAttribute('aria-pressed', String(selected));
    b.textContent = s === 'Alla' ? `Alla grossister (${{afterCat.length}})` : `${{s}} (${{supCounts[s]}})`;
    b.onclick = () => {{
      if (s === 'Alla') activeSuppliers.clear();
      else if (activeSuppliers.has(s)) activeSuppliers.delete(s);
      else activeSuppliers.add(s);
      renderB2B();
    }};
    chipBox.appendChild(b);
  }});

  const rows = afterCat.filter(x =>
    !activeSuppliers.size || visibleSuppliers(x).length
  );
  rows.sort((a, b) => {{
    if (sortMode === 'spend_desc') {{
      return accumulatedSpend(b, activeSuppliers) - accumulatedSpend(a, activeSuppliers)
        || purchaseCount(b, activeSuppliers) - purchaseCount(a, activeSuppliers)
        || a.vara.localeCompare(b.vara, 'sv');
    }}
    if (sortMode === 'name') {{
      return a.vara.localeCompare(b.vara, 'sv') || a.unit.localeCompare(b.unit, 'sv');
    }}
    return purchaseCount(b, activeSuppliers) - purchaseCount(a, activeSuppliers)
      || a.vara.localeCompare(b.vara, 'sv')
      || a.unit.localeCompare(b.unit, 'sv');
  }});

  const vatLbl = showInclVat ? 'inkl. moms' : 'exkl. moms';
  document.getElementById('metaLbl').textContent =
    `Uppdaterad: ${{B2B.generated_at || ''}} • ${{rows.length}} varor (${{vatLbl}})`;

  const box = document.getElementById('listBox');
  if (!rows.length) {{
    box.innerHTML = onlyStock
      ? '<div class="card">Du har inte fyllt i några mängder i förrådet ännu. Klicka på "← Visa alla varor" ovan och skriv in hur många kg / L / st som finns!</div>'
      : '<div class="card">Inga B2B-varor matchar sökningen eller filtret.</div>';
    return;
  }}

  box.innerHTML = rows.map(x => {{
    const supsList = visibleSuppliers(x);
    const inventoryPrice = getUnitPrices(x);
    const p = !activeSuppliers.size || supsList.some(s => s.grossist === inventoryPrice.supName)
      ? inventoryPrice
      : getCatalogPrices(x, supsList);
    const mainPrice = showInclVat ? p.gross : p.net;
    const avgPrice = showInclVat ? p.avgG : p.avgN;
    const inventoryUnitPrice = showInclVat ? inventoryPrice.gross : inventoryPrice.net;
    const isMulti = supsList.length > 1;
    const isH = !!openHist[x.id];
    const curQ = Number(invQty[x.id] || 0);
    const isCustom = String(x.id).startsWith('cust_');
    const allCardSups = [...new Set((x.history || []).map(h => h.supplier).concat(supsList.map(s => s.grossist)))];
    const historySuppliers = histSups[x.id]
      ? new Set(histSups[x.id])
      : activeSuppliers;
    const supFilteredHist = (x.history || []).filter(h =>
      !historySuppliers.size || historySuppliers.has(h.supplier)
    );
    const allHistMonths = [...new Set(supFilteredHist.map(h => String(h.date || '').slice(0, 7)).filter(Boolean))].sort().reverse();
    const activeMonth = allHistMonths.includes(histMonth[x.id]) ? histMonth[x.id] : '';
    const histRows = activeMonth
      ? supFilteredHist.filter(h => String(h.date || '').startsWith(activeMonth))
      : supFilteredHist;
    const totalPurchases = purchaseCount(x, historySuppliers);
    const histCount = totalPurchases > histRows.length
      ? `${{histRows.length}} av ${{totalPurchases}}`
      : String(histRows.length);
    const histTitle = historySuppliers.size === 1
      ? `Prishistorik för ${{esc([...historySuppliers][0])}}`
      : 'Prishistorik';

    let supHtml = '';
    if (isMulti) {{
      supHtml = `<div class="sup-list">` + supsList.map((s, idx) => {{
        const sp = showInclVat ? s.latest_gross : s.latest_net;
        const isChosen = p.supName === s.grossist;
        return `<div class="sup-row ${{idx === 0 ? 'best' : ''}} ${{isChosen ? 'chosen' : ''}}" title="Klicka för att räkna med denna grossists pris" onclick="selectSupForVara('${{x.id}}', '${{esc(s.grossist)}}')">` +
          `<span>${{isChosen ? '✓ ' : (idx === 0 ? '🟢 ' : '')}}<span class="notranslate">${{esc(s.grossist)}}</span> <span style="font-weight:400;color:#64748b">(${{esc(s.datum)}})</span></span>` +
          `<span class="notranslate">${{fmtSv(sp)}} kr/${{esc(x.unit)}}</span>` +
        `</div>`;
      }}).join('') + `</div>`;
    }} else {{
      const s = supsList.find(st => st.grossist === p.supName) || {{}};
      supHtml = `<div class="sub"><span class="sup-tag notranslate">${{esc(p.supName)}}</span> ${{s.artikel && s.artikel !== x.vara ? esc(s.artikel) + ' • ' : ''}}${{s.forp ? esc(s.forp) + ' • ' : ''}}Senast: ${{esc(s.datum || x.latest_date)}}</div>`;
    }}

    let histHtml = '';
    if (isH) {{
      const showAck = !!histShowAck[x.id];
      const packModeH = isPackMode(x);
      const cumTotals = new Array(histRows.length).fill(0);
      const cumPrices = new Array(histRows.length).fill(0);
      let runQ = 0;
      let runKr = 0;
      for (let i = histRows.length - 1; i >= 0; i--) {{
        const h = histRows[i];
        const hp = showInclVat ? h.price_gross : h.price_net;
        const lTot = showInclVat ? (h.line_gross ?? (Number(h.qty || 0) * hp)) : (h.line_net ?? (Number(h.qty || 0) * hp));
        runQ += Number(h.qty || 0);
        runKr += Number(lTot || 0);
        cumTotals[i] = Math.round(runQ * 1000) / 1000;
        cumPrices[i] = Math.round(runKr * 100) / 100;
      }}
      const fmtSingleUnit = (baseQ) => {{
        if (packModeH) {{
          const pk = Math.round((baseQ / Number(x.pack_qty)) * 100) / 100;
          return `${{fmtQtySv(pk)}} ${{x.pack_unit}}`;
        }}
        return `${{fmtQtySv(baseQ)}} ${{x.unit}}`;
      }};
      const totalHistQ = (!historySuppliers.size && !activeMonth && x.total_qty && histRows.length >= (x.kop || 0))
        ? Number(x.total_qty)
        : (cumTotals.length ? cumTotals[0] : 0);
      const totalHistKr = cumPrices.length ? cumPrices[0] : 0;
      const totalHistLbl = (showAck && totalHistQ > 0)
        ? ` • Totalt: ${{esc(fmtSingleUnit(totalHistQ))}}${{totalHistKr > 0 ? ' • ' + fmtSv(totalHistKr) + ' kr' : ''}}`
        : '';
      const ackBtn = `<button class="mini-btn" style="padding:2px 7px;font-size:11px;margin-left:6px" onclick="toggleHistAck('${{x.id}}')">${{showAck ? 'Dölj ack.' : '📊 Visa ack.'}}</button>`;
      const supPillsHtml = allCardSups.length > 1
        ? `<div style="display:flex;flex-wrap:wrap;gap:4px;margin:4px 0 4px">` + allCardSups.map(sn => {{
            const on = !historySuppliers.size || historySuppliers.has(sn);
            return `<button class="chip notranslate ${{on ? 'cat-chip active' : ''}}" style="padding:2px 8px;font-size:11px" onclick="toggleHistSup('${{x.id}}', '${{esc(sn)}}')">${{on ? '✓ ' : ''}}${{esc(sn)}}</button>`;
          }}).join('') + `</div>`
        : '';
      const monthPillsHtml = allHistMonths.length > 1
        ? `<div style="display:flex;flex-wrap:wrap;gap:4px;margin:4px 0 6px">` +
          `<button class="chip notranslate ${{!activeMonth ? 'active' : ''}}" style="padding:2px 8px;font-size:11px" onclick="toggleHistMonth('${{x.id}}', '')">Alla mån</button>` +
          allHistMonths.map(ym => `<button class="chip notranslate ${{activeMonth === ym ? 'active' : ''}}" style="padding:2px 8px;font-size:11px" onclick="toggleHistMonth('${{x.id}}', '${{ym}}')">${{ym}}</button>`).join('') +
          `</div>`
        : '';
      histHtml = `<div class="hist-box"><div style="display:flex;justify-content:space-between;align-items:center;font-weight:700;margin-bottom:4px;"><span>${{histTitle}} (${{vatLbl}})<span class="notranslate" style="color:#0369a1">${{totalHistLbl}}</span></span>${{ackBtn}}</div>${{supPillsHtml}}${{monthPillsHtml}}` +
        histRows.map((h, idx) => {{
          const hp = showInclVat ? h.price_gross : h.price_net;
          const lineTot = showInclVat ? (h.line_gross ?? (Number(h.qty || 0) * hp)) : (h.line_net ?? (Number(h.qty || 0) * hp));
          const clickAttr = h.doc_id ? `onclick="openInvoiceModal(${{h.doc_id}}, ${{h.line_id || 0}})"` : '';
          const linkPill = h.doc_id ? `<span class="inv-link-pill">📄 Faktura →</span>` : '';
          const rq = Number(h.qty || 0);
          const cq = cumTotals[idx] || 0;
          const ckr = cumPrices[idx] || 0;
          const qtyText = rq > 0
            ? (showAck ? `${{esc(fmtSingleUnit(rq))}} • Ack: ${{esc(fmtSingleUnit(cq))}}${{ckr > 0 ? ' (' + fmtSv(ckr) + ' kr)' : ''}}` : `${{esc(fmtSingleUnit(rq))}}`)
            : '';
          const unitSub = packModeH
            ? `${{fmtSv(hp * Number(x.pack_qty))}} kr/${{esc(x.pack_unit)}}`
            : `${{fmtSv(hp)}} kr/${{esc(h.unit)}}`;
          const priceHtml = lineTot > 0
            ? `<div style="text-align:right;white-space:nowrap"><b class="notranslate" style="font-size:13px;color:#0f172a">${{fmtSv(lineTot)}} kr</b><div class="hist-art notranslate">${{unitSub}}</div></div>`
            : `<b class="notranslate" style="white-space:nowrap;text-align:right">${{unitSub}}</b>`;
          return `<div class="hist-row" ${{clickAttr}}>` +
            `<div><div>${{esc(h.date)}} • <b class="notranslate">${{esc(h.supplier)}}</b>${{linkPill}}</div><div class="hist-art">${{esc(h.artikel)}}${{qtyText ? ' • <b style="color:#0f172a">' + qtyText + '</b>' : ''}}</div></div>` +
            priceHtml +
          `</div>`;
        }}).join('') + (histRows.length ? '' : '<div>Inga tillgängliga historikrader.</div>') +
        `</div>`;
    }}

    const delBtn = isCustom ? `<button class="mini-btn danger" style="padding:4px 8px;font-size:11px" onclick="deleteCustomItem('${{x.id}}')">Ta bort</button>` : '';
    const packMode = isPackMode(x);
    const dispQ = getDisplayQty(x, curQ);
    const activeUnit = packMode ? x.pack_unit : x.unit;
    const otherUnit = packMode ? x.unit : x.pack_unit;
    const unitCtrlHtml = hasPack(x)
      ? `<button class="unit-toggle notranslate" onclick="toggleUnitMode('${{x.id}}')" title="Byt räknenhet (${{esc(activeUnit)}} ↔ ${{esc(otherUnit)}})">${{esc(activeUnit)}} ⇄ ${{esc(otherUnit)}}</button>` +
        `<span id="peq_${{x.id}}" class="pack-sub notranslate">${{
          curQ > 0
            ? (packMode ? '= ' + fmtQtySv(curQ) + ' ' + esc(x.unit) : '= ' + fmtQtySv(Math.round((curQ / Number(x.pack_qty)) * 100) / 100) + ' ' + esc(x.pack_unit))
            : ''
        }}</span>`
      : `<span class="unit-pill notranslate">${{esc(x.unit)}}</span>`;
    const priceMainHtml = packMode
      ? `<div class="p-main notranslate">${{fmtSv(mainPrice * Number(x.pack_qty))}} kr/${{esc(x.pack_unit)}}</div><div class="p-avg notranslate">à ${{fmtQtySv(x.pack_qty)}} ${{esc(x.unit)}}</div>`
      : `<div class="p-main notranslate">${{fmtSv(mainPrice)}} kr/${{esc(x.unit)}}</div><div class="p-avg notranslate">Snitt: ${{fmtSv(avgPrice)}} kr/${{esc(x.unit)}}</div>`;

    const spendTot = sortMode === 'spend_desc' ? accumulatedSpend(x, activeSuppliers) : 0;
    const spendTagHtml = (sortMode === 'spend_desc' && spendTot > 0)
      ? `<span class="multi-tag notranslate" style="background:#fef3c7;color:#92400e">💰 ${{fmtSv(spendTot)}} kr</span>`
      : '';

    return `<div id="card_${{x.id}}" class="card ${{isMulti ? 'multi' : ''}} ${{curQ > 0 ? 'counted' : ''}}">
      <div class="info">
        <div style="display:flex;align-items:center;gap:4px;flex-wrap:wrap">
          <span class="cat-tag">${{esc(x.category || 'Övrigt')}}</span>
          ${{isMulti ? `<span class="multi-tag">${{supsList.length}} grossister</span>` : ''}}
          ${{spendTagHtml}}
          ${{delBtn}}
        </div>
        <div class="title">${{esc(x.vara)}}</div>
        ${{supHtml}}
        <div class="inv-ctrl">
          <span class="inv-lbl">I förråd:</span>
          <button class="step-btn notranslate" onclick="stepQty('${{x.id}}', -1)">−</button>
          <input id="qinp_${{x.id}}" class="qty-inp notranslate" type="number" step="any" min="0" inputmode="decimal" placeholder="0" value="${{dispQ > 0 ? dispQ : ''}}" oninput="onQtyInput('${{x.id}}', this.value)">
          ${{unitCtrlHtml}}
          <button class="step-btn notranslate" onclick="stepQty('${{x.id}}', 1)">+</button>
          <span id="lval_${{x.id}}" class="line-val notranslate ${{curQ > 0 ? 'show' : ''}}">${{curQ > 0 ? '= ' + fmtSv(curQ * inventoryUnitPrice) + ' kr' : ''}}</span>
        </div>
        ${{histHtml}}
      </div>
      <div class="actions">
        <div>
          ${{priceMainHtml}}
        </div>
        <button class="hist-btn ${{isH ? 'open' : ''}}" onclick="toggleHist('${{x.id}}')">📈 Historik (${{histCount}})</button>
      </div>
    </div>`;
  }}).join('');
}}

function setLang(lang) {{
  if (lang === 'sv') {{
    document.cookie = 'googtrans=; path=/; expires=Thu, 01 Jan 1970 00:00:00 GMT';
    document.cookie = 'googtrans=; path=/; domain=' + location.hostname + '; expires=Thu, 01 Jan 1970 00:00:00 GMT';
  }} else {{
    document.cookie = 'googtrans=/sv/' + lang + '; path=/';
    document.cookie = 'googtrans=/sv/' + lang + '; path=/; domain=' + location.hostname;
  }}
  try {{ localStorage.setItem('kt_cloud_lang', lang); }} catch(e) {{}}
  location.reload();
}}

function googleTranslateElementInit() {{
  new google.translate.TranslateElement({{
    pageLanguage: 'sv',
    includedLanguages: 'zh-CN,hr',
    autoDisplay: false
  }}, 'google_translate_element');
}}

let curB2bTab = 'inv';
let spCat = 'Alla';
let spMonth = '';
const spSups = new Set();
let spSortMode = 'kr_desc';
let spOpenHist = {{}};
let spOpenCats = {{}};
let spOpenMain = {{}};

function switchB2bTab(tab) {{
  curB2bTab = tab === 'spend' ? 'spend' : 'inv';
  document.getElementById('tabInvBtn').classList.toggle('active', curB2bTab === 'inv');
  document.getElementById('tabSpendBtn').classList.toggle('active', curB2bTab === 'spend');
  document.getElementById('viewInv').style.display = curB2bTab === 'inv' ? '' : 'none';
  document.getElementById('viewSpend').style.display = curB2bTab === 'spend' ? '' : 'none';
  if (curB2bTab === 'spend') renderSpend();
}}

function spendItemStats(x) {{
  const rows = (x.history || []).filter(h =>
    (!spSups.size || spSups.has(h.supplier)) &&
    (!spMonth || String(h.date || '').startsWith(spMonth))
  );
  let kr = 0, qty = 0;
  rows.forEach(h => {{
    const hp = showInclVat ? h.price_gross : h.price_net;
    const lt = showInclVat ? (h.line_gross ?? (Number(h.qty || 0) * hp)) : (h.line_net ?? (Number(h.qty || 0) * hp));
    kr += Number(lt || 0);
    qty += Number(h.qty || 0);
  }});
  if (!spSups.size && !spMonth) {{
    const totKr = showInclVat ? Number(x.total_gross || 0) : Number(x.total_net || 0);
    if (totKr > 0) kr = totKr;
    if (Number(x.total_qty || 0) > 0) qty = Number(x.total_qty);
  }}
  const kop = (!spSups.size && !spMonth) ? Number(x.kop || rows.length) : rows.length;
  return {{ kr: Math.round(kr * 100) / 100, qty: Math.round(qty * 1000) / 1000, kop, rows }};
}}

function renderSpend() {{
  const items = B2B.items || [];
  const q = (document.getElementById('spQInput').value || '').trim().toLowerCase();
  const vatLbl = showInclVat ? 'inkl. moms' : 'exkl. moms';
  document.getElementById('btnSpVat').textContent = showInclVat ? 'Visar: Inkl. moms' : 'Visar: Exkl. moms';

  const months = [...new Set(items.flatMap(x => (x.history || []).map(h => String(h.date || '').slice(0, 7))).filter(Boolean))].sort().reverse();
  document.getElementById('spMonthChips').innerHTML =
    `<button class="chip cat-chip ${{!spMonth ? 'active' : ''}}" onclick="spMonth='';renderSpend()">Alla månader</button>` +
    months.map(m => `<button class="chip cat-chip notranslate ${{spMonth === m ? 'active' : ''}}" onclick="spMonth=(spMonth==='${{m}}'?'':'${{m}}');renderSpend()">${{m}}</button>`).join('');

  const sups = [...new Set(items.flatMap(x => (x.suppliers || []).map(s => s.grossist)))].sort();
  document.getElementById('spSupChips').innerHTML =
    `<button class="chip ${{!spSups.size ? 'active' : ''}}" onclick="spSups.clear();renderSpend()">Alla</button>` +
    sups.map(s => `<button class="chip notranslate ${{spSups.has(s) ? 'active' : ''}}" onclick="spSups.has('${{esc(s)}}')?spSups.delete('${{esc(s)}}'):spSups.add('${{esc(s)}}');renderSpend()">${{esc(s)}}</button>`).join('');

  const enriched = items.map(x => ({{ x, st: spendItemStats(x) }})).filter(o => o.st.kop > 0 && o.st.kr > 0);
  const searched = q
    ? enriched.filter(o => {{
        const hay = `${{o.x.vara}} ${{o.x.category}} ${{(o.x.suppliers || []).map(s => s.grossist + ' ' + s.artikel).join(' ')}}`.toLowerCase();
        return hay.includes(q);
      }})
    : enriched;

  const catMap = {{}};
  searched.forEach(o => {{
    const c = o.x.category || 'Övrigt';
    catMap[c] = (catMap[c] || 0) + o.st.kr;
  }});
  const catsSorted = Object.entries(catMap).sort((a, b) => b[1] - a[1]);
  document.getElementById('spCatChips').innerHTML =
    `<button class="chip cat-chip ${{spCat === 'Alla' ? 'active' : ''}}" onclick="spCat='Alla';renderSpend()">Alla</button>` +
    catsSorted.map(([c]) => `<button class="chip cat-chip ${{spCat === c ? 'active' : ''}}" onclick="spCat='${{esc(c)}}';renderSpend()">${{esc(c)}}</button>`).join('');

  document.getElementById('spCatGrid').innerHTML = catsSorted.map(([c, val]) =>
    `<button class="cat-pill ${{spCat === c ? 'active' : ''}}" onclick="spCat=(spCat==='${{esc(c)}}'?'Alla':'${{esc(c)}}');renderSpend()"><span>${{esc(c)}}</span><b>${{fmtSv(val)}} kr</b></button>`
  ).join('');

  const filtered = spCat === 'Alla' ? searched : searched.filter(o => (o.x.category || 'Övrigt') === spCat);
  filtered.sort((a, b) => {{
    if (spSortMode === 'qty_desc') return b.st.qty - a.st.qty || b.st.kr - a.st.kr;
    if (spSortMode === 'kop_desc') return b.st.kop - a.st.kop || b.st.kr - a.st.kr;
    if (spSortMode === 'name_asc') return a.x.vara.localeCompare(b.x.vara, 'sv');
    return b.st.kr - a.st.kr || b.st.kop - a.st.kop;
  }});

  const grandKr = filtered.reduce((acc, o) => acc + o.st.kr, 0);
  const grandKop = filtered.reduce((acc, o) => acc + o.st.kop, 0);
  document.getElementById('spSumMain').textContent = `📊 Totalt inköpt: ${{fmtSv(grandKr)}} kr (${{vatLbl}})`;
  document.getElementById('spSumSub').textContent = `${{filtered.length}} varor • ${{grandKop}} inköpsrader${{spMonth ? ' • ' + spMonth : ''}}${{spCat !== 'Alla' ? ' • ' + spCat : ''}}`;

  const box = document.getElementById('spListBox');
  if (!filtered.length) {{
    box.innerHTML = '<div class="card">Inga inköp matchar valt filter.</div>';
    return;
  }}

  // Nivå 1: Huvudrubriker -> Nivå 2: Underkategorier -> Nivå 3: Varor
  const getMainGroup = (cat) => {{
    if (cat === 'Kött & Fågel' || cat === 'Fisk & Skaldjur') return '🥩 Kött, Fågel & Fisk';
    if (cat === 'Alkohol') return '🍺 Alkohol';
    if (cat === 'Läsk' || cat === 'Vatten') return '🥤 Läsk & Vatten';
    if (cat === 'Olja & Bas' || cat === 'Ris' || cat === 'Nudlar' || cat === 'Sjögräs' || cat === 'Bröd & Bakning') return '🍚 Torrvaror, Olja & Ris';
    if (cat === 'Frukt & Grönt' || cat === 'Mejeri & Ägg') return '🥬 Frukt, Grönt & Mejeri';
    if (cat === 'Såser & Konserver' || cat === 'Kryddor & Buljong') return '🥫 Såser, Konserver & Kryddor';
    if (cat === 'Fryst & Halvfabrikat') return '❄️ Fryst & Halvfabrikat';
    return '📦 Förbrukning & Övrigt';
  }};

  const getSubCat = (x) => {{
    const c = x.category || 'Övrigt';
    const v = (x.vara || '').toLowerCase();
    if (c === 'Kött & Fågel') {{
      if (/anka|duck/.test(v)) return '🦆 Anka';
      if (/kyckling|chicken/.test(v)) return '🐔 Kyckling';
      if (/fläsk|skink|bacon|sidfläsk|spareribs|serrano|gris|broskben|falukorv|cevapcicci/.test(v)) return '🐷 Fläsk & Chark';
      return '🐄 Nötkött';
    }}
    if (c === 'Fisk & Skaldjur') {{
      if (/bläckfisk|squid|sepia|masago/.test(v)) return '🦑 Bläckfisk & Rom';
      if (/räk|shrimp|krabba|havskräfta|scallop|oyster/.test(v)) return '🦐 Räkor & Skaldjur';
      return '🐟 Lax & Fisk';
    }}
    if (c === 'Alkohol') {{
      if (/vin\b|vino|prosecco/.test(v)) return '🍷 Vin & Prosecco';
      if (/vodka|likör|jäg/.test(v)) return '🥃 Sprit & Likör';
      return '🍺 Öl & Cider';
    }}
    if (c === 'Frukt & Grönt') {{
      if (/apelsin|banan|citron|avokado|melon|cantaloupe|piel de sapo/.test(v)) return '🍉 Frukt & Melon';
      if (/potatis|lök|purjolök|vitlök|morot|morötter|rättika|ingefära/.test(v)) return '🥔 Potatis, Lök & Rotfrukter';
      if (/basilika|koriander|persilja|chili|rawit|spansk peppar|kål|spetskål|pak choi|broccoli|blomkål/.test(v)) return '🌶️ Örter, Chili & Kål';
      return '🍅 Grönsaker & Svamp';
    }}
    if (c === 'Såser & Konserver') {{
      if (/soja|soy|fisk|fish sauce|ostron|oyster|hoisin/.test(v)) return '🥢 Soja, Fisk- & Ostronsås';
      if (/curry|chili|sriracha|sambal|tom yum|miso|hot pot|broad bean|barbecue|black bean/.test(v)) return '🌶️ Curry, Chili- & Wokpastor';
      if (/kokosmjölk|bambuskott|baby corn|majskorn|persik|pineapple|cornichon|gurka|pickled|inari|tomatpur/.test(v)) return '🥥 Kokosmjölk & Konserver';
      return '🍶 Vinäger, Mayo & Övriga såser';
    }}
    if (c === 'Fryst & Halvfabrikat') {{
      if (/gyoza|dumpling|ha kauw|wonton|vårrull|spring roll|mantou/.test(v)) return '🥟 Dumplings, Gyoza & Vårrullar';
      return '🍟 Pommes, Fiskbollar & Övrigt';
    }}
    if (c === 'Förbrukning & Emballage') {{
      if (/microform|sushiform|delibägare|dressingbägare|soppbägare|take away|lock/.test(v)) return '🥡 Takeaway-lådor, Lock & Bägare';
      if (/kasse|påse|planpase|sopsäck|kanister/.test(v)) return '🛍️ Påsar & Kassar';
      if (/servett|serv |handduk|torkrulle|torkpapper|rengöring|svamp|stålbollar|sprayflaska|bakpapper|matfilm|handsk/.test(v)) return '🧻 Papper, Handskar & Städ';
      return '✏️ Tillbehör & Kontor';
    }}
    return c;
  }};

  const mainMap = {{}};
  filtered.forEach(o => {{
    const origCat = o.x.category || 'Övrigt';
    const mg = getMainGroup(origCat);
    const subCat = getSubCat(o.x);
    if (!mainMap[mg]) mainMap[mg] = {{ name: mg, kr: 0, kop: 0, itemCount: 0, subs: {{}} }};
    if (!mainMap[mg].subs[subCat]) mainMap[mg].subs[subCat] = {{ cat: subCat, kr: 0, kop: 0, items: [] }};
    mainMap[mg].kr += o.st.kr;
    mainMap[mg].kop += o.st.kop;
    mainMap[mg].itemCount += 1;
    mainMap[mg].subs[subCat].kr += o.st.kr;
    mainMap[mg].subs[subCat].kop += o.st.kop;
    mainMap[mg].subs[subCat].items.push(o);
  }});
  const mainGroups = Object.values(mainMap).sort((a, b) => b.kr - a.kr);
  const maxMainKr = mainGroups.length ? Math.max(...mainGroups.map(g => g.kr)) : 1;

  box.innerHTML = mainGroups.map((mg, mIdx) => {{
    const mgPct = grandKr > 0 ? (mg.kr / grandKr) * 100 : 0;
    const mgBarW = maxMainKr > 0 ? Math.max(2, (mg.kr / maxMainKr) * 100) : 0;
    const isMainOpen = !!spOpenMain[mg.name] || spCat !== 'Alla' || Boolean(q);

    let subsHtml = '';
    if (isMainOpen) {{
      const subGroups = Object.values(mg.subs).sort((a, b) => b.kr - a.kr);
      const maxSubKr = subGroups.length ? Math.max(...subGroups.map(s => s.kr)) : 1;
      subsHtml = `<div style="margin-top:10px;display:flex;flex-direction:column;gap:8px">` + subGroups.map(grp => {{
        const subPct = mg.kr > 0 ? (grp.kr / mg.kr) * 100 : 0;
        const subBarW = maxSubKr > 0 ? Math.max(2, (grp.kr / maxSubKr) * 100) : 0;
        const isSubOpen = !!spOpenCats[grp.cat] || spCat !== 'Alla' || Boolean(q);

        let itemsHtml = '';
        if (isSubOpen) {{
          itemsHtml = `<div style="margin-top:8px">` + grp.items.map((o, idx) => {{
            const x = o.x;
            const st = o.st;
            const qtyTxt = hasPack(x)
              ? `${{fmtQtySv(Math.round((st.qty / Number(x.pack_qty)) * 100) / 100)}} ${{esc(x.pack_unit)}} (${{fmtQtySv(st.qty)}} ${{esc(x.unit)}})`
              : `${{fmtQtySv(st.qty)}} ${{esc(x.unit)}}`;
            const avgUnitKr = st.qty > 0 ? st.kr / st.qty : 0;
            const avgTxt = hasPack(x)
              ? `Snitt: ${{fmtSv(avgUnitKr * Number(x.pack_qty))}} kr/${{esc(x.pack_unit)}}`
              : `Snitt: ${{fmtSv(avgUnitKr)}} kr/${{esc(x.unit)}}`;
            const itemPct = grp.kr > 0 ? (st.kr / grp.kr) * 100 : 0;
            const isH = !!spOpenHist[x.id];

            const histHtml = isH
              ? `<div class="hist-box" style="margin-top:6px">` + st.rows.map(h => {{
                  const hp = showInclVat ? h.price_gross : h.price_net;
                  const lt = showInclVat ? (h.line_gross ?? (Number(h.qty || 0) * hp)) : (h.line_net ?? (Number(h.qty || 0) * hp));
                  const rq = Number(h.qty || 0);
                  const rQtyTxt = hasPack(x)
                    ? `${{fmtQtySv(Math.round((rq / Number(x.pack_qty)) * 100) / 100)}} ${{esc(x.pack_unit)}} (${{fmtQtySv(rq)}} ${{esc(x.unit)}})`
                    : `${{fmtQtySv(rq)}} ${{esc(x.unit)}}`;
                  const clickAttr = h.doc_id ? `onclick="openInvoiceModal(${{h.doc_id}}, ${{h.line_id || 0}})"` : '';
                  const linkPill = h.doc_id ? `<span class="inv-link-pill">📄 Faktura →</span>` : '';
                  return `<div class="hist-row" ${{clickAttr}}><div><div><b>${{esc(h.date)}}</b> • <span class="notranslate">${{esc(h.supplier)}}</span>${{linkPill}}</div><div class="hist-art">${{esc(h.artikel)}} • <b>${{rQtyTxt}}</b></div></div><b class="notranslate" style="white-space:nowrap">${{fmtSv(lt)}} kr</b></div>`;
                }}).join('') + `</div>`
              : '';

            return `<div style="padding:7px 0;border-top:1px dashed #e2e8f0">
              <div style="display:flex;justify-content:space-between;align-items:flex-start;gap:10px">
                <div style="min-width:0;flex:1">
                  <div style="font-weight:700;font-size:13.5px;color:#0f172a">${{idx + 1}}. ${{esc(x.vara)}}</div>
                  <div class="sub notranslate" style="margin-top:2px"><b>${{qtyTxt}}</b> • ${{st.kop}} köp • ${{avgTxt}}</div>
                </div>
                <div style="text-align:right;flex-shrink:0" class="notranslate">
                  <div style="font-weight:800;font-size:13.5px;color:#0f172a">${{fmtSv(st.kr)}} kr</div>
                  <div style="font-size:11px;color:#64748b">${{itemPct.toFixed(1).replace('.', ',')}}% av ${{esc(grp.cat)}}</div>
                </div>
              </div>
              <button class="mini-btn" style="padding:2px 8px;font-size:11px;margin-top:4px" onclick="spOpenHist['${{x.id}}']=!spOpenHist['${{x.id}}'];renderSpend()">${{isH ? 'Dölj köp' : '📈 Visa ' + st.rows.length + ' köp'}}</button>
              ${{histHtml}}
            </div>`;
          }}).join('') + `</div>`;
        }}

        return `<div style="background:#f8fafc;border:1px solid #cbd5e1;border-left:4px solid #0284c7;border-radius:10px;padding:10px 12px">
          <div style="display:flex;justify-content:space-between;align-items:center;gap:10px;cursor:pointer" onclick="spOpenCats['${{esc(grp.cat)}}']=!spOpenCats['${{esc(grp.cat)}}'];renderSpend()">
            <div>
              <div style="font-weight:800;font-size:14.5px;color:#0f172a">${{isSubOpen ? '▼' : '▶'}} ${{esc(grp.cat)}}</div>
              <div class="sub" style="margin-top:1px">${{grp.items.length}} varor • ${{grp.kop}} köp</div>
            </div>
            <div style="text-align:right;flex-shrink:0" class="notranslate">
              <div style="font-weight:800;font-size:15px;color:#0f172a">${{fmtSv(grp.kr)}} kr</div>
              <div style="font-size:11px;color:#64748b">${{subPct.toFixed(1).replace('.', ',')}}%</div>
            </div>
          </div>
          <div class="spend-bar-bg" style="margin-top:6px"><div class="spend-bar-fill" style="width:${{subBarW.toFixed(1)}}%"></div></div>
          ${{itemsHtml}}
        </div>`;
      }}).join('') + `</div>`;
    }}

    return `<div class="card" style="display:block;border-left:6px solid #0f172a">
      <div style="display:flex;justify-content:space-between;align-items:center;gap:12px;cursor:pointer" onclick="spOpenMain['${{esc(mg.name)}}']=!spOpenMain['${{esc(mg.name)}}'];renderSpend()">
        <div>
          <span class="rank-badge">#${{mIdx + 1}}</span>
          <span style="font-size:17px;font-weight:800;color:#0f172a">${{isMainOpen ? '▼' : '▶'}} ${{esc(mg.name)}}</span>
          <div class="sub" style="margin-top:2px">${{Object.keys(mg.subs).length}} underkategorier • ${{mg.itemCount}} varor • ${{mg.kop}} köp</div>
        </div>
        <div style="text-align:right;flex-shrink:0" class="notranslate">
          <div class="p-main" style="font-size:18px">${{fmtSv(mg.kr)}} kr</div>
          <div class="p-avg">${{mgPct.toFixed(1).replace('.', ',')}}% av total</div>
        </div>
      </div>
      <div class="spend-bar-bg" style="margin-top:8px"><div class="spend-bar-fill" style="width:${{mgBarW.toFixed(1)}}%;background:#0f172a"></div></div>
      ${{subsHtml}}
    </div>`;
  }}).join('');
}}

(function() {{
  let curLang = 'sv';
  try {{ curLang = localStorage.getItem('kt_cloud_lang') || 'sv'; }} catch(e) {{}}
  const map = {{ 'sv': 'langSv', 'zh-CN': 'langZh', 'hr': 'langHr' }};
  const el = document.getElementById(map[curLang] || 'langSv');
  if (el) el.classList.add('active');
  if (curLang !== 'sv') {{
    document.cookie = 'googtrans=/sv/' + curLang + '; path=/';
  }}
}})();

let migrationFailed = false;
try {{ migrateInventory(); }} catch(e) {{ migrationFailed = true; }}
showInventoryMonth();
if (migrationFailed) inventoryStatus('Kunde inte föra över den tidigare inventeringen.', true);
window.addEventListener('storage', e => {{
  if (e.storageArea === localStorage && (e.key === inventoryPrefix + inventoryMonth || e.key === null)) showInventoryMonth();
}});
</script>
<script src="https://translate.google.com/translate_a/element.js?cb=googleTranslateElementInit"></script>
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
    (PUBLIC_DIR / ".gitattributes").write_text("*.pdf binary\n*.jpg binary\n*.jpeg binary\n*.png binary\n", encoding="utf-8")
    (PUBLIC_DIR / "index.html").write_text(
        "<!doctype html><html><head><meta name='robots' content='noindex'></head><body>OK</body></html>",
        encoding="utf-8",
    )
    (slug_dir / "index.html").write_text(html, encoding="utf-8")
    b2b_file = BASELINES_FILE.parent / "b2b_pricelist.json"
    if b2b_file.exists():
        import shutil
        b2b_payload = json.loads(b2b_file.read_text(encoding="utf-8"))
        b2b_dir = slug_dir / "b2b"
        b2b_dir.mkdir(parents=True, exist_ok=True)
        (b2b_dir / "index.html").write_text(build_b2b_html(b2b_payload), encoding="utf-8")
        src_docs = BASELINES_FILE.parent / "b2b_docs"
        if src_docs.exists():
            dst_docs = b2b_dir / "docs"
            dst_docs.mkdir(parents=True, exist_ok=True)
            for f in src_docs.iterdir():
                if f.is_file():
                    shutil.copy2(f, dst_docs / f.name)
    print(f"Klart! Byggde {len(deals)} kampanjer ({sum(1 for d in deals if d['verdict_code'] == 'GREEN')} gröna klipp) -> {slug_dir / 'index.html'}")


if __name__ == "__main__":
    main()
