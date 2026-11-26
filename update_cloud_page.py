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
