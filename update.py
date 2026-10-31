"""ดึงเลขรางวัลที่ 1 "ทุกงวดย้อนหลัง" จากเว็บ Sanook แล้วต่อท้าย lottery_all_history.txt

วิธีทำงาน
  0) อ่านหน้าหลัก https://news.sanook.com/lotto/ ก่อน (งวดล่าสุด; ถ้าหน้าไม่ระบุวันที่ จะใช้ตัวเลือกเดิม
     lotto__number แล้วยืนยันวันที่จากหน้ารายงวด)
  1) อ่านหน้าสรุปผลย้อนหลังของ Sanook ทีละหน้า  https://news.sanook.com/lotto/archive/ (page/2/, page/3/ ...)
     เพื่อเติมงวดเก่าที่หน้าหลักไม่แสดง แต่ละหน้ามีทั้งวันที่และเลขรางวัลที่ 1 ของหลายงวด
  2) งวดที่เพิ่งพบใหม่ (สูงสุด 6 งวดล่าสุด) จะเปิดหน้ารายงวดของงวดนั้นมาเทียบอีกครั้ง
     ถ้าสองหน้าให้เลขไม่ตรงกัน จะไม่บันทึกงวดนั้นและแจ้งเตือนใน LAST_WARNINGS
  3) เก็บผลไว้ใน lottery_sanook_cache.json ครั้งถัดไปจะอ่านแค่หน้าแรก ๆ จนเจองวดที่เคยเก็บแล้วก็หยุด
  4) ถ้าอ่านหน้าสรุปไม่ได้ จะลองหน้ารายงวดของ 3 งวดล่าสุดแทน
Sanook เคยตอบกลับด้วยการเด้งซ้ำ (redirect loop) เมื่อไม่มีคุกกี้ จึงใช้ Session เก็บคุกกี้
และแวะหน้าแรกของเว็บก่อนลองใหม่อัตโนมัติ
  5) (เพิ่ม) ข้อมูลเชื่อถือได้จาก GLO ผ่าน API ทางการที่ GLO เปิดให้นักพัฒนา
     (POST https://www.glo.or.th/api/checking/getLotteryResult  — ตามเอกสารใน gdcatalog.glo.or.th)
       - เติมงวด "เก่ากว่า" ที่ Sanook มี (ย้อนไปจนกว่า GLO จะไม่มีข้อมูล)
       - เทียบ 6 งวดล่าสุดกับ Sanook ถ้าไม่ตรงกันจะแจ้งเตือนและ "คงเลขของ Sanook ไว้" ไม่เขียนทับ
     ไม่ได้อ่านหน้าเว็บ glo.or.th (เว็บนั้นไม่อนุญาตให้บอตเข้า) ปิดส่วนนี้ได้โดยตั้ง USE_GLO = False
ถ้าล้มเหลวจะเก็บสาเหตุไว้ใน LAST_ERRORS เพื่อแสดงให้ผู้ใช้เห็น
"""
import json
import os
import re
import sys
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime
from urllib.parse import urljoin

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE_FILE = os.path.join(HERE, "lottery_sanook_cache.json")
HISTORY_FILE = os.path.join(HERE, "lottery_all_history.txt")
BACKUP_FILE = os.path.join(HERE, "lottery_all_history.backup.txt")   # สำเนาไฟล์เดิมก่อนเรียงใหม่ครั้งแรก
REPORT_FILE = os.path.join(HERE, "lottery_verify_report.txt")        # รายงานเทียบกับ Sanook/GLO
GLO_CACHE_FILE = os.path.join(HERE, "lottery_glo_cache.json")
GLO_DEBUG_FILE = os.path.join(HERE, "lottery_glo_debug.json")        # ตัวอย่างคำตอบ GLO ที่อ่านไม่ได้ (ส่งให้ผู้พัฒนาดูได้)

USE_GLO = True
GLO_URL = "https://www.glo.or.th/api/checking/getLotteryResult"
GLO_VERIFY_NEWEST = 6        # เทียบกี่งวดล่าสุดกับ GLO ทุกครั้งที่รัน
GLO_MISS_LIMIT = 36          # ถ้าหางวดไม่เจอติดกันเท่านี้ครั้ง (~1.5 ปี) ถือว่า GLO ไม่มีข้อมูลเก่ากว่านี้แล้ว
GLO_MAX_YEARS_BACK = 35      # เพดานย้อนหลังจากงวดเก่าสุดของ Sanook
GLO_DELAY = 0.25             # วินาที เว้นระหว่างการเรียก API ไม่ให้ถี่เกินไป

HOME = "https://news.sanook.com/"
MAIN = "https://news.sanook.com/lotto/"
ARCHIVE = "https://news.sanook.com/lotto/archive/"
CHECK = "https://news.sanook.com/lotto/check/{d:02d}{m:02d}{y}/"  # ปีเป็น พ.ศ.
MAX_PAGES = 150
VERIFY_MAX = 6
PAGE_DELAY = 0.3  # วินาที เว้นระยะระหว่างการอ่านแต่ละหน้า ไม่ให้ถี่เกินไป

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "th,en;q=0.8",
    "Referer": HOME,
}
SESSION = requests.Session()
SESSION.headers.update(HEADERS)
SESSION.max_redirects = 10

MONTHS = [
    "มกราคม", "กุมภาพันธ์", "มีนาคม", "เมษายน", "พฤษภาคม", "มิถุนายน",
    "กรกฎาคม", "สิงหาคม", "กันยายน", "ตุลาคม", "พฤศจิกายน", "ธันวาคม",
]
_MONTHS_RE = "|".join(MONTHS)
# เลขรางวัลที่ 1 (ไม่นับ "รางวัลข้างเคียงรางวัลที่ 1")
_PRIZE1 = r"(?<!เคียง)รางวัลที่\s*1\s*(?:รางวัลละ\s*6,000,000\s*บาท\s*)?(\d{6})(?!\d)"
# วันที่อาจเขียนเว้นวรรค ("16 พฤษภาคม 2550") หรือเป็นหัวข้อแบบมีขีด ("งวดประจำวันที่-16-พฤษภาคม-2550")
_SEP = r"[\s\-–_]*"
_DRAW_RE = re.compile(
    rf"(\d{{1,2}}){_SEP}({_MONTHS_RE}){_SEP}(\d{{4}})\D{{0,120}}?{_PRIZE1}", re.S
)
_PAGE_LINK_RE = re.compile(r'href="([^"#]*?/lotto/archive/[^"#]*?)"')

_LOCK = threading.Lock()   # ป้องกันตัวนับ/สถานะที่ใช้ร่วมกันระหว่างเธรดตอนดึงรางวัลอื่นพร้อมกัน
LAST_ERRORS = []
LAST_WARNINGS = []
LAST_GLO = {"enabled": False, "added": 0, "checked": 0, "conflicts": [], "floor": "", "oldest": "", "error": ""}
LAST_STATS = {"index": 0, "fetched": 0, "resolved": 0, "failed": 0, "pages": 0, "oldest": "", "newest": "", "complete": False, "stop": ""}
MAX_ERRORS_SHOWN = 6


def _err(msg):
    if len(LAST_ERRORS) < MAX_ERRORS_SHOWN:
        LAST_ERRORS.append(msg)
    elif len(LAST_ERRORS) == MAX_ERRORS_SHOWN:
        LAST_ERRORS.append("… และข้อผิดพลาดอื่น ๆ ในลักษณะเดียวกัน")


def thai_date(d):
    return f"{d.day} {MONTHS[d.month - 1]} {d.year + 543}"


def _get(url):
    """อ่านหน้าเว็บ ถ้าโดนเด้งวนซ้ำ ให้แวะหน้าแรกเพื่อรับคุกกี้แล้วลองใหม่"""
    last = None
    for attempt in range(3):
        try:
            r = SESSION.get(url, timeout=20)
            r.raise_for_status()
            r.encoding = "utf-8"
            return r.text
        except requests.exceptions.TooManyRedirects as e:
            last = e
            try:
                SESSION.get(HOME, timeout=20)  # รับคุกกี้จากหน้าแรก
            except requests.exceptions.RequestException:
                pass
        except requests.exceptions.HTTPError as e:
            if e.response is not None and e.response.status_code in (404, 410):
                raise
            last = e
        except requests.exceptions.RequestException as e:
            last = e
        time.sleep(0.5 * (attempt + 1))
    raise last


def _to_text(html):
    html = re.sub(r"(?is)<(script|style)\b.*?</\1>", " ", html)
    return re.sub(r"<[^>]+>", " ", html)


# ---------------------------------------------------------------- อ่านหน้าเว็บ
def parse_archive_page(html):
    """คืน dict {date: เลขรางวัลที่ 1} ที่พบในหน้า (ถ้าวันเดียวกันได้เลขต่างกันจะคืนเป็น set หลายค่า)"""
    found = {}
    for dd, mon, yy, num in _DRAW_RE.findall(_to_text(html)):
        try:
            d = date(int(yy) - 543, MONTHS.index(mon) + 1, int(dd))
        except ValueError:
            continue
        found.setdefault(d, set()).add(num)
    return found


def parse_check_page(html, d):
    """หน้ารายงวด: คืนเลขรางวัลที่ 1 ของงวด d (None ถ้าไม่ใช่หน้าของงวดนี้/อ่านไม่ได้)"""
    text = _to_text(html)
    if thai_date(d) not in text:
        return None
    m = re.search(_PRIZE1, text)
    return m.group(1) if m else None


def fetch_check(d):
    url = CHECK.format(d=d.day, m=d.month, y=d.year + 543)
    try:
        return parse_check_page(_get(url), d)
    except requests.exceptions.RequestException:
        return None


def recent_draw_dates(today=None, count=3):
    """เดาวันออกรางวัล (1 และ 16) ล่าสุด ใช้เฉพาะตอนอ่านหน้าสรุปไม่ได้ เรียงจากเก่าไปใหม่"""
    today = today or date.today()
    out, y, m = [], today.year, today.month
    while len(out) < count + 2:
        for dd in (16, 1):
            cand = date(y, m, dd)
            if cand <= today:
                out.append(cand)
        m, y = (12, y - 1) if m == 1 else (m - 1, y)
    out.sort(reverse=True)
    return sorted(out[:count])


# ---------------------------------------------------------------- แคช
def load_cache():
    """คืน dict {YYYYMMDD: เลข} และคีย์พิเศษ "_complete" = เคยอ่านหน้าย้อนหลังครบทุกหน้าแล้ว"""
    try:
        with open(CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return {}
    out = {k: v for k, v in data.items() if re.fullmatch(r"\d{8}", k) and re.fullmatch(r"\d{6}", str(v))}
    if data.get("_complete") and out:
        out["_complete"] = "1"
    return out


def save_cache(cache):
    try:
        tmp = CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, sort_keys=True)
        os.replace(tmp, CACHE_FILE)
    except OSError as e:
        _err(f"บันทึกแคชไม่สำเร็จ ({e})")


# ---------------------------------------------------------------- ตัวหลัก
def _next_page_url(html, base_url, n):
    """หาลิงก์ไปหน้า n+1 จากหน้าปัจจุบัน (กันกรณีรูปแบบ URL เปลี่ยน) ถ้าไม่เจอใช้รูปแบบ /page/N/"""
    for href in _PAGE_LINK_RE.findall(html):
        m = re.search(r"(?:/page/|[?&]page=|/archive/)(\d+)/?$", href.rstrip())
        if m and int(m.group(1)) == n + 1:
            return urljoin(base_url, href)
    return f"{ARCHIVE}page/{n + 1}/"


def crawl_archive(cache, progress=None):
    """อ่านหน้าสรุปย้อนหลังไปเรื่อย ๆ จนสุดหน้า คืน (found, complete)
    complete=True เมื่ออ่านจนสุดหน้าสุดท้ายจริง ๆ ถึงจะยอมให้รอบหน้าหยุดเมื่อเจองวดที่เก็บไว้แล้ว"""
    found, url, complete, skipped = {}, ARCHIVE, False, []
    LAST_STATS["stop"] = ""
    for n in range(1, MAX_PAGES + 1):
        try:
            html = _get(url)
        except requests.exceptions.HTTPError as e:
            if n > 1 and e.response is not None and e.response.status_code in (404, 410):
                complete = True  # เลยหน้าสุดท้ายแล้ว
                LAST_STATS["stop"] = f"จบที่หน้า {n - 1}"
            else:
                LAST_STATS["stop"] = f"หน้า {n} เปิดไม่ได้"
                _err(f"Sanook หน้า {n}: {e}")
            break
        except requests.exceptions.RequestException as e:
            LAST_STATS["stop"] = f"หน้า {n} เชื่อมต่อไม่สำเร็จ"
            _err(f"Sanook หน้า {n}: เชื่อมต่อไม่สำเร็จ ({e})")
            break
        page = parse_archive_page(html)
        if not page:
            if "รางวัลที่ 1" in html or "รางวัลที่1" in html:
                # หน้ามีผลหวยอยู่ แต่อ่านวันที่ไม่ออก: ข้ามหน้านี้ ไม่ถือว่าหมดหน้า
                skipped.append(n)
                LAST_WARNINGS.append(f"หน้า {n} มีผลหวยแต่อ่านวันที่ไม่ได้ จึงข้ามหน้านี้")
                if n == 1 or len(skipped) >= 3:
                    LAST_STATS["stop"] = "อ่านวันที่ไม่ได้ต่อเนื่องหลายหน้า (รูปแบบหน้าเว็บอาจเปลี่ยน)"
                    break
                url = _next_page_url(html, url, n)
                time.sleep(PAGE_DELAY)
                continue
            if n > 1:
                complete = True
                LAST_STATS["stop"] = f"หน้า {n} ไม่มีงวดแล้ว (จบที่หน้า {n - 1})"
            else:
                LAST_STATS["stop"] = "หน้าแรกไม่พบงวดใดเลย (รูปแบบหน้าเว็บอาจเปลี่ยน)"
                _err("Sanook หน้าสรุปย้อนหลัง: อ่านได้ แต่ไม่พบวันที่/เลขรางวัลที่ 1 ในหน้า")
            break
        if all(d in found for d in page):
            complete = True  # เว็บส่งหน้าเดิมซ้ำ = หมดหน้าแล้ว
            LAST_STATS["stop"] = f"หน้า {n} ซ้ำกับหน้าก่อน (จบที่หน้า {n - 1})"
            break
        for d, nums in page.items():
            found.setdefault(d, set()).update(nums)
        LAST_STATS["pages"] = n
        if progress:
            progress(n, 0)
        if cache.get("_complete") and all(f"{d:%Y%m%d}" in cache for d in page):
            complete = True
            LAST_STATS["stop"] = f"ถึงช่วงที่เก็บไว้แล้วที่หน้า {n}"
            break
        url = _next_page_url(html, url, n)
        time.sleep(PAGE_DELAY)
    else:
        LAST_STATS["stop"] = f"ครบ {MAX_PAGES} หน้าตามเพดานที่ตั้งไว้"
    return found, complete


def read_main_page(found):
    """อ่านหน้าหลัก https://news.sanook.com/lotto/ แล้วเพิ่มงวดที่พบลงใน found (date -> set ของเลข)"""
    try:
        html = _get(MAIN)
    except requests.exceptions.RequestException as e:
        _err(f"Sanook หน้าหลัก: เชื่อมต่อไม่สำเร็จ ({e})")
        return
    page = parse_archive_page(html)
    for d, nums in page.items():
        found.setdefault(d, set()).update(nums)
    if page:
        return
    # หน้าไม่ระบุวันที่ข้างเลข: ใช้ตัวเลือกเดิมของ update.py แล้วยืนยันวันที่จากหน้ารายงวด
    m = re.search(r'class="[^"]*lotto__number[^"]*"[^>]*>\s*(\d{6})\s*<', html)
    if not m:
        _err("Sanook หน้าหลัก: อ่านได้ แต่ไม่พบเลขรางวัลที่ 1")
        return
    n = m.group(1)
    for d in reversed(recent_draw_dates()):
        if fetch_check(d) == n:
            found.setdefault(d, set()).add(n)
            return
    LAST_WARNINGS.append(f"หน้าหลัก Sanook แสดง {n} แต่ยืนยันวันที่ของงวดไม่ได้ จึงยังไม่บันทึกเลขนี้")


def get_all_lotteries(progress=None, fresh=False):
    """ดึงทุกงวดย้อนหลัง คืนรายการเลขรางวัลที่ 1 เรียงจากเก่าไปใหม่
    progress(done, total) ถูกเรียกระหว่างอ่านหน้า (total=0 หมายถึงยังไม่รู้จำนวนหน้าทั้งหมด)"""
    LAST_ERRORS.clear()
    LAST_WARNINGS.clear()
    cache = {} if fresh else load_cache()
    was_complete = bool(cache.get("_complete"))
    LAST_STATS.update(index=0, fetched=0, resolved=0, failed=0, pages=0, oldest="", newest="", complete=False, stop="")
    found = {}
    read_main_page(found)
    arch, complete = crawl_archive(cache, progress)
    for d, nums in arch.items():
        found.setdefault(d, set()).update(nums)
    LAST_STATS.update(index=len(found))

    if not found:  # สำรอง: หน้ารายงวดของ 3 งวดล่าสุด
        for d in recent_draw_dates():
            n = fetch_check(d)
            if n:
                found[d] = {n}
        if found:
            LAST_WARNINGS.append("อ่านหน้าสรุปย้อนหลังไม่ได้ จึงตรวจได้เฉพาะ 3 งวดล่าสุดจากหน้ารายงวด")
        else:
            _err("Sanook: อ่านผลไม่ได้ทั้งหน้าสรุปย้อนหลังและหน้ารายงวด")

    new_dates = sorted(d for d in found if f"{d:%Y%m%d}" not in cache)
    LAST_STATS["fetched"] = len(new_dates)
    verify_set = set(new_dates[-VERIFY_MAX:])
    for d in new_dates:
        nums = found[d]
        if len(nums) > 1:
            LAST_STATS["failed"] += 1
            LAST_WARNINGS.append(f"งวด {thai_date(d)}: พบเลขรางวัลที่ 1 หลายค่าในหน้าเดียวกัน ({', '.join(sorted(nums))}) จึงไม่บันทึก")
            continue
        n = next(iter(nums))
        if d in verify_set:
            other = fetch_check(d)  # เทียบกับหน้ารายงวด (ถ้าเปิดไม่ได้ ใช้ค่าจากหน้าสรุป)
            if other and other != n:
                LAST_STATS["failed"] += 1
                LAST_WARNINGS.append(
                    f"งวด {thai_date(d)}: หน้าสรุปได้ {n} แต่หน้ารายงวดได้ {other} ไม่ตรงกัน จึงไม่บันทึกงวดนี้"
                )
                continue
        cache[f"{d:%Y%m%d}"] = n
        LAST_STATS["resolved"] += 1
    if complete or was_complete:
        cache["_complete"] = "1"
    else:
        cache.pop("_complete", None)
    all_keys = sorted(k for k in cache if k != "_complete")
    if all_keys:
        LAST_STATS.update(
            oldest=thai_date(date(int(all_keys[0][:4]), int(all_keys[0][4:6]), int(all_keys[0][6:]))),
            newest=thai_date(date(int(all_keys[-1][:4]), int(all_keys[-1][4:6]), int(all_keys[-1][6:]))),
        )
    LAST_STATS["complete"] = bool(cache.get("_complete"))
    if new_dates or cache.get("_complete") != (load_cache().get("_complete")):
        save_cache(cache)
    return [cache[k] for k in all_keys]


def get_recent_lotteries():
    """เข้ากันได้กับโค้ดเดิม: ตอนนี้คือดึงทุกงวด"""
    return get_all_lotteries()


def get_latest_lottery():
    found = get_all_lotteries()
    return found[-1] if found else None


# ---------------------------------------------------------------- GLO (API ทางการ)
GLO_SESSION = requests.Session()
GLO_SESSION.headers.update({
    "User-Agent": HEADERS["User-Agent"],
    "Accept": "application/json, text/plain, */*",
    "Content-Type": "application/json",
    "Origin": "https://www.glo.or.th",
    "Referer": "https://www.glo.or.th/",
})


def _find_key(payload, key):
    """หาค่าของคีย์ key ในโครงสร้าง JSON ซ้อนกัน (คืนค่าแรกที่เจอ)"""
    if isinstance(payload, dict):
        if key in payload:
            return payload[key]
        for v in payload.values():
            r = _find_key(v, key)
            if r is not None:
                return r
    elif isinstance(payload, list):
        for v in payload:
            r = _find_key(v, key)
            if r is not None:
                return r
    return None


def parse_glo_date(text):
    """แปลง displayDate ของ GLO เป็น date (รองรับ ISO, dd/mm/yyyy และ '1 มีนาคม 2567'); ไม่รู้จักรูปแบบ -> None"""
    t = str(text)
    m = re.search(r"(\d{4})-(\d{1,2})-(\d{1,2})", t)
    try:
        if m:
            y = int(m.group(1))
            return date(y - 543 if y > 2400 else y, int(m.group(2)), int(m.group(3)))
        m = re.search(r"(\d{1,2})\s*/\s*(\d{1,2})\s*/\s*(\d{4})", t)
        if m:
            y = int(m.group(3))
            return date(y - 543 if y > 2400 else y, int(m.group(2)), int(m.group(1)))
        m = re.search(rf"(\d{{1,2}})\s*({_MONTHS_RE})\s*(\d{{4}})", t)
        if m:
            y = int(m.group(3))
            return date(y - 543 if y > 2400 else y, MONTHS.index(m.group(2)) + 1, int(m.group(1)))
    except ValueError:
        return None
    return None


def glo_first_prize(payload, d):
    """คืน (สถานะ, เลข) สถานะ: ok / miss (งวดนี้ไม่มี) / mismatch (คำตอบเป็นของวันอื่น) / unreadable"""
    first = _find_key(payload, "first")
    if first is None:
        first = _find_key(payload, "prizeFirst")
    if first is None:
        return "miss", None
    found = set(re.findall(r"(?<!\d)\d{6}(?!\d)", json.dumps(first)))
    if len(found) != 1:
        return ("miss", None) if not found else ("unreadable", None)
    shown = _find_key(payload, "displayDate")
    if shown is not None:
        got = parse_glo_date(shown)
        if got is None:
            return "unreadable", None
        if got != d:
            return "mismatch", None   # API ตอบงวดอื่นกลับมา (เช่นงวดล่าสุด) ห้ามนำมาใช้
    return "ok", found.pop()


def _save_glo_debug(d, payload):
    try:
        if not os.path.exists(GLO_DEBUG_FILE):
            with open(GLO_DEBUG_FILE, "w", encoding="utf-8") as f:
                json.dump({"requested": d.isoformat(), "response": json.dumps(payload, ensure_ascii=False)[:4000]}, f, ensure_ascii=False)
    except OSError:
        pass


def fetch_glo_draw(d):
    """เรียก API ทางการของ GLO สำหรับวันที่ d คืน (สถานะ, เลข) สถานะ: ok / miss / fail / unreadable / mismatch"""
    try:
        r = GLO_SESSION.post(
            GLO_URL, json={"date": f"{d.day:02d}", "month": f"{d.month:02d}", "year": str(d.year)}, timeout=20
        )
        if r.status_code in (400, 404, 422):
            return "miss", None  # วันนั้นไม่มีการออกรางวัล
        r.raise_for_status()
        payload = r.json()
    except requests.exceptions.RequestException as e:
        LAST_GLO["error"] = f"เรียก API ไม่สำเร็จ ({e})"
        return "fail", None
    except ValueError:
        LAST_GLO["error"] = "API ตอบกลับมาไม่ใช่ JSON"
        return "fail", None
    status, n = glo_first_prize(payload, d)
    if status in ("unreadable", "mismatch"):
        _save_glo_debug(d, payload)
    return status, n


def load_glo_cache():
    try:
        with open(GLO_CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return {}
    out = {k: v for k, v in data.items() if re.fullmatch(r"\d{8}", k) and re.fullmatch(r"\d{6}", str(v))}
    if re.fullmatch(r"\d{8}", str(data.get("_floor", ""))):
        out["_floor"] = data["_floor"]
    return out


def save_glo_cache(cache):
    try:
        tmp = GLO_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, sort_keys=True)
        os.replace(tmp, GLO_CACHE_FILE)
    except OSError as e:
        _err(f"บันทึกแคช GLO ไม่สำเร็จ ({e})")


def _month_last_day(y, m):
    nxt = date(y + (m == 12), 1 if m == 12 else m + 1, 1)
    return (nxt - __import__("datetime").timedelta(days=1)).day


def glo_candidates(y, m, nominal):
    """วันที่ที่เป็นไปได้ของงวด 'nominal' (1 หรือ 16) ของเดือน m/ปี y รวมกรณีเลื่อนวัน เช่น 2, 17, 30 ธ.ค."""
    out = [date(y, m, nominal)]
    if nominal == 1:
        out += [date(y, m, 2), date(y, m, 3)]
        py, pm = (y - 1, 12) if m == 1 else (y, m - 1)
        last = _month_last_day(py, pm)
        out += [date(py, pm, last), date(py, pm, last - 1)]
    else:
        out += [date(y, m, 17), date(y, m, 18), date(y, m, 15)]
    return out


def _nominals_before(d):
    """(ปี, เดือน, 1|16) ย้อนหลังต่อจากงวดของวันที่ d ทีละงวด"""
    y, m, nom = d.year, d.month, (1 if d.day <= 8 else 16)
    if d.day >= 29:  # เช่น 30 ธ.ค. = งวดที่เลื่อนมาจากวันที่ 1 ของเดือนถัดไป
        y, m, nom = (y + (m == 12), 1 if m == 12 else m + 1, 1)
    while True:
        if nom == 16:
            nom = 1
        else:
            nom = 16
            y, m = (y - 1, 12) if m == 1 else (y, m - 1)
        yield y, m, nom


def extend_with_glo(progress=None, verify_all=False):
    """เติมงวดที่เก่ากว่า Sanook จาก GLO และเทียบงวดล่าสุดกับ Sanook (ไม่เขียนทับเลขของ Sanook)"""
    LAST_GLO.update(enabled=bool(USE_GLO), added=0, checked=0, conflicts=[], floor="", oldest="", error="")
    if not USE_GLO:
        return
    sanook = {k: v for k, v in load_cache().items() if k != "_complete"}
    if not sanook:
        LAST_GLO["error"] = "ยังไม่มีข้อมูล Sanook เป็นฐาน จึงยังไม่ได้ใช้ GLO"
        return
    cache = load_glo_cache()
    skeys = sorted(sanook)
    earliest = date(int(skeys[0][:4]), int(skeys[0][4:6]), int(skeys[0][6:]))
    known = set(k for k in list(cache) + list(sanook) if k != "_floor")
    fails = 0

    def abort(msg):
        LAST_GLO["error"] = msg
        LAST_WARNINGS.append("GLO: " + msg)

    # (1) งวดที่เก่ากว่างวดเก่าสุดของ Sanook
    if "_floor" not in cache:
        misses, hits = 0, 0
        limit_year = earliest.year - GLO_MAX_YEARS_BACK
        stop_reason = None
        for y, m, nom in _nominals_before(earliest):
            if y < limit_year:
                stop_reason = "floor"
                break
            hit = False
            for cand in glo_candidates(y, m, nom):
                key = f"{cand:%Y%m%d}"
                if key in known:
                    hit = True
                    break
                time.sleep(GLO_DELAY)
                status, n = fetch_glo_draw(cand)
                if status == "fail":
                    fails += 1
                    if fails >= 4:
                        abort("API ของ GLO ใช้ไม่ได้ติดต่อกันหลายครั้ง จึงข้ามส่วนนี้ — " + LAST_GLO["error"])
                        stop_reason = "abort"
                        break
                    continue
                fails = 0
                if status == "ok":
                    cache[key] = n
                    known.add(key)
                    hits += 1
                    hit = True
                    if progress:
                        progress(hits, 0)
                    if hits % 20 == 0:
                        save_glo_cache(cache)
                    break
                if status in ("unreadable", "mismatch") and not LAST_GLO["error"]:
                    LAST_GLO["error"] = "คำตอบของ GLO อ่านไม่ได้/เป็นของวันอื่น (ดูตัวอย่างใน lottery_glo_debug.json)"
            if stop_reason:
                break
            misses = 0 if hit else misses + 1
            if misses >= GLO_MISS_LIMIT:
                stop_reason = "floor"
                break
        if stop_reason == "floor":
            cache["_floor"] = f"{y:04d}{m:02d}{nom:02d}"
        LAST_GLO["added"] = hits
        save_glo_cache(cache)

    # (2) เทียบกับ Sanook
    targets = skeys if verify_all else skeys[-GLO_VERIFY_NEWEST:]
    for key in targets:
        if key in cache:
            got = cache[key]
        else:
            if fails >= 4:
                break
            d = date(int(key[:4]), int(key[4:6]), int(key[6:]))
            time.sleep(GLO_DELAY)
            status, got = fetch_glo_draw(d)
            if status == "fail":
                fails += 1
                if fails >= 4:
                    abort("API ของ GLO ใช้ไม่ได้ติดต่อกันหลายครั้ง จึงข้ามการเทียบ — " + LAST_GLO["error"])
                continue
            fails = 0
            if status != "ok":
                continue
            cache[key] = got
        LAST_GLO["checked"] += 1
    save_glo_cache(cache)
    gkeys = sorted(k for k in cache if k != "_floor")
    if gkeys:
        LAST_GLO["oldest"] = thai_date(date(int(gkeys[0][:4]), int(gkeys[0][4:6]), int(gkeys[0][6:])))
    LAST_GLO["floor"] = cache.get("_floor", "")
    for d, sn, gl in glo_conflicts():
        LAST_WARNINGS.append(f"งวด {thai_date(d)}: Sanook ได้ {sn} แต่ GLO ได้ {gl} ไม่ตรงกัน (ในไฟล์ใช้เลขของ Sanook)")


def glo_conflicts():
    """[(date, เลข Sanook, เลข GLO)] ของงวดที่ทั้งสองแหล่งมีแต่เลขไม่ตรงกัน"""
    sk, gl = load_cache(), load_glo_cache()
    out = []
    for k, v in gl.items():
        if k != "_floor" and k in sk and sk[k] != v:
            out.append((date(int(k[:4]), int(k[4:6]), int(k[6:])), sk[k], v))
    return sorted(out)


# ---------------------------------------------------------------- ประวัติ: เรียงใหม่สุดไว้บนสุด + ตรวจกับ Sanook
# ---------------------------------------------------------------- รางวัลอื่น: เลขหน้า 3 ตัว / เลขท้าย 3 ตัว / เลขท้าย 2 ตัว
# แหล่งที่ 1: PPTVHD36  https://www.pptvhd36.com/lotto/check?date=YYYY-MM-DD   (หน้านี้แสดงทุกรางวัลของงวดนั้นในหน้าเดียว)
# แหล่งที่ 2: Sanook     https://news.sanook.com/lotto/check/DDMMYYYY/          (สำรอง ถ้าแหล่งแรกอ่านไม่ได้)
# ทีละงวด แล้วเก็บแคชไว้
# ผลรวมอยู่ในไฟล์ lottery_all_prizes.csv (เรียงงวดใหม่สุดไว้บนสุด) คอลัมน์: date,first,front3,back3,last2
PRIZES_CACHE_FILE = os.path.join(HERE, "lottery_prizes_cache.json")
PRIZES_CSV_FILE = os.path.join(HERE, "lottery_all_prizes.csv")
PRIZES_DEBUG_FILE = os.path.join(HERE, "lottery_prize_debug.txt")   # ตัวอย่างหน้าที่อ่านไม่ได้ (ส่งให้ผู้พัฒนาดูได้)
USE_PRIZES = True
PRIZE_WORKERS = 3
PRIZE_DELAY = 0.2           # วินาที เว้นระยะระหว่างคำขอ ไม่ให้ถี่เกินไป
PRIZE_MAX_ERRORS = 8        # เปิดหน้ารายงวดไม่ได้ติดกันเท่านี้ครั้งโดยไม่เคยสำเร็จ -> ข้ามขั้นตอนนี้
PRIZE_SOURCES = ("pptv", "sanook")   # ลำดับการลอง
PPTV_URL = "https://www.pptvhd36.com/lotto/check?date={d:%Y-%m-%d}"
LAST_PRIZES = {"enabled": False, "total": 0, "new": 0, "failed": 0, "mismatch": 0, "odd": 0, "error": "",
               "nodate": 0, "noparse": 0, "http": 0, "by_source": {}}

# รางวัลที่ 1 แบบผ่อนปรน: รองรับ "รางวัลที่ 1 : 011781" และ "รางวัลที่ 1 รางวัลละ 6,000,000 บาท 011781"
_PRIZE1_LOOSE = r"(?<!เคียง)รางวัลที่\s*1[\s:：]*(?:รางวัลละ\s*6,000,000\s*บาท[\s:：]*)?(\d{6})(?!\d)"
_PRIZE_STOP = r"(?:เลขหน้า\s*3\s*ตัว|เลขท้าย\s*3\s*ตัว|เลขท้าย\s*2\s*ตัว|รางวัลข้างเคียง|รางวัลที่\s*2)"


def _segment(tail, label_re):
    """ข้อความหลังป้าย label_re จนถึงป้ายถัดไป (ไม่เกิน 200 ตัวอักษร)"""
    m = re.search(label_re, tail)
    if not m:
        return None
    rest = tail[m.end():]
    n = re.search(_PRIZE_STOP, rest)
    return rest[: min(n.start(), 200)] if n else rest[:200]


def _numbers(seg, width, expect=None):
    """เลข width หลักในข้อความ (ไม่นับตัวเลขที่เป็นส่วนของจำนวนเงิน เช่น 4,000 หรือ 6,000,000 แต่นับ "060, 521" ที่คั่นด้วยจุลภาค)
    ถ้าเลขติดกันเป็นก้อนเดียว เช่น "402392" และรู้จำนวนที่คาดไว้ (expect) จะแบ่งให้"""
    toks = re.findall(rf"(?<![\d.])(?<!\d,)\d{{{width}}}(?![\d.])(?!,\d{{3}})", seg or "")
    if toks or not expect:
        return toks
    for run in re.findall(r"(?<![\d.,])\d+(?![\d.,])", seg or ""):
        if len(run) == width * expect:
            return [run[i:i + width] for i in range(0, len(run), width)]
    return []


def parse_prizes_text(text):
    """จากข้อความหน้ารายงวด คืน {"f","f3","b3","l2"} หรือ None ถ้าอ่านไม่ได้
    เริ่มอ่านหลังรางวัลที่ 1 เพื่อไม่ไปติดข้อความโปรยหัวข้อที่กล่าวถึงรางวัลเหล่านี้ซ้ำ ๆ"""
    m = re.search(_PRIZE1_LOOSE, text)
    if not m:
        return None
    tail = text[m.end():]
    f3 = _numbers(_segment(tail, r"เลขหน้า\s*3\s*ตัว"), 3, 2)
    b3 = _numbers(_segment(tail, r"เลขท้าย\s*3\s*ตัว"), 3, 2)
    l2 = _numbers(_segment(tail, r"เลขท้าย\s*2\s*ตัว"), 2, 1)
    if not f3 or not b3 or not l2:
        return None
    return {"f": m.group(1), "f3": f3[:4], "b3": b3[:4], "l2": l2[0]}


_ABBR = ["ม.ค.", "ก.พ.", "มี.ค.", "เม.ย.", "พ.ค.", "มิ.ย.", "ก.ค.", "ส.ค.", "ก.ย.", "ต.ค.", "พ.ย.", "ธ.ค."]


def _date_present(text, d):
    """หน้านั้นระบุวันที่ของงวด d จริงหรือไม่ (รองรับ 16 ตุลาคม 2569 / 16 ต.ค. 69 / 16/10/69 / 16/10/2569)"""
    if thai_date(d) in text:
        return True
    be, yy = d.year + 543, (d.year + 543) % 100
    pats = [rf"(?<!\d){d.day}\s*{re.escape(_ABBR[d.month - 1])}\s*(?:{be}|{yy:02d})(?!\d)",
            rf"(?<!\d)0?{d.day}\s*/\s*0?{d.month}\s*/\s*(?:{be}|{yy:02d})(?!\d)"]
    return any(re.search(p, text) for p in pats)


def diagnose_check(html, d):
    """คืน (ผลที่อ่านได้ หรือ None, เหตุผลถ้าอ่านไม่ได้: 'nodate' | 'noparse', ข้อความล้วนของหน้า)"""
    text = _to_text(html)
    if not _date_present(text, d):
        return None, "nodate", text
    got = parse_prizes_text(text)
    return got, ("" if got else "noparse"), text


def parse_check_prizes(html, d):
    return diagnose_check(html, d)[0]


PPTV_SESSION = requests.Session()
PPTV_SESSION.headers.update({
    "User-Agent": HEADERS["User-Agent"],
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "th,en;q=0.8",
})
_PPTV_HEAD = re.compile(
    rf"งวดประจำวันที่\s*(\d{{1,2}})\s*({_MONTHS_RE})\s*(\d{{4}})[\s#*]{{0,30}}รางวัลที่\s*1\s*(?:มี\s*1\s*)?รางวัล\S{{0,3}}\s*ละ\s*6,000,000\s*บาท"
)
_PPTV_FIRST = re.compile(r"(?<![\d,.])(\d)\s+(\d)\s+(\d)\s+(\d)\s+(\d)\s+(\d)(?![\d,])|(?<![\d,.])(\d{6})(?!\d)")


def _get_pptv(url):
    last = None
    for attempt in range(3):
        try:
            r = PPTV_SESSION.get(url, timeout=20)
            r.raise_for_status()
            r.encoding = "utf-8"
            return r.text
        except requests.exceptions.HTTPError as e:
            if e.response is not None and e.response.status_code in (404, 410):
                raise
            last = e
        except requests.exceptions.RequestException as e:
            last = e
        time.sleep(0.5 * (attempt + 1))
    raise last


def parse_pptv_text(text, d):
    """หน้า PPTV: คืน (ผล, เหตุผล) ผล = {"f","f3","b3","l2"} หรือ None
    หน้านี้มีรายชื่อทุกงวดอยู่ก่อนผลรางวัล จึงต้องยืนยันวันที่จากหัวข้อที่อยู่ติดกับรางวัลที่ 1 เท่านั้น
    (ถ้าขอวันที่ที่ไม่มี เว็บอาจแสดงงวดล่าสุดแทน) และรางวัลที่ 1 อาจแสดงทีละหลัก เช่น "0 1 1 7 8 1" """
    m = _PPTV_HEAD.search(text)
    if not m:
        return None, "noparse"
    try:
        shown = date(int(m.group(3)) - 543, MONTHS.index(m.group(2)) + 1, int(m.group(1)))
    except ValueError:
        return None, "noparse"
    if shown != d:
        return None, "nodate"
    tail = text[m.end():]
    mf = _PPTV_FIRST.search(tail[:300])
    if not mf:
        return None, "noparse"
    first = "".join(mf.groups()[:6]) if mf.group(1) else mf.group(7)
    f3 = _numbers(_segment(tail, r"เลขหน้า\s*3\s*ตัว"), 3, 2)
    b3 = _numbers(_segment(tail, r"เลขท้าย\s*3\s*ตัว"), 3, 2)
    l2 = _numbers(_segment(tail, r"เลขท้าย\s*2\s*ตัว"), 2, 1)
    if not f3 or not b3 or not l2:
        return None, "noparse"
    return {"f": first, "f3": f3[:4], "b3": b3[:4], "l2": l2[0]}, ""


def load_prizes_cache():
    try:
        with open(PRIZES_CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return {}
    ok = {}
    for k, v in data.items():
        if (re.fullmatch(r"\d{8}", k) and isinstance(v, dict) and re.fullmatch(r"\d{6}", str(v.get("f", "")))
                and v.get("f3") and v.get("b3") and re.fullmatch(r"\d{2}", str(v.get("l2", "")))):
            ok[k] = v
    return ok


def save_prizes_cache(cache):
    try:
        tmp = PRIZES_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, sort_keys=True)
        os.replace(tmp, PRIZES_CACHE_FILE)
    except OSError as e:
        _err(f"บันทึกแคชรางวัลอื่นไม่สำเร็จ ({e})")


def _save_prize_debug(d, reason, text, source=""):
    try:
        i = text.find("รางวัลที่ 1")
        start = max(i, 0) if reason == "noparse" else 0
        excerpt = re.sub(r"\n\s*\n+", "\n", re.sub(r"[ \t]+", " ", text[start:start + 1500]))
        why = "ไม่พบวันที่ของงวดในหน้า" if reason == "nodate" else "พบหน้าแต่อ่านเลขหน้า/ท้าย 3 ตัวและท้าย 2 ตัวไม่ได้"
        with open(PRIZES_DEBUG_FILE, "a", encoding="utf-8") as f:
            f.write(f"=== [{source}] {thai_date(d)} : {why} (ความยาวข้อความ {len(text)}) ===\n{excerpt}\n\n")
    except OSError:
        pass


def _try_source(source, d):
    """('error', None, '', ข้อความ) | ('miss', ...) | ('page', ผล หรือ None, เหตุผล, ข้อความหน้า)"""
    try:
        html = _get_pptv(PPTV_URL.format(d=d)) if source == "pptv" else _get(CHECK.format(d=d.day, m=d.month, y=d.year + 543))
    except requests.exceptions.HTTPError as e:
        if e.response is not None and e.response.status_code in (404, 410):
            return "miss", None, "", ""
        return "error", None, "", str(e)
    except requests.exceptions.RequestException as e:
        return "error", None, "", str(e)
    if source == "pptv":
        text = _to_text(html)
        got, reason = parse_pptv_text(text, d)
        return "page", got, reason, text
    got, reason, text = diagnose_check(html, d)
    return "page", got, reason, text


def update_prizes(progress=None, fresh=False):
    """ดึงเลขหน้า 3 ตัว/ท้าย 3 ตัว/ท้าย 2 ตัวของทุกงวดที่ Sanook มี (เฉพาะงวดที่ยังไม่มีในแคช)
    ลองตามลำดับ PRIZE_SOURCES ทุกงวดจะเทียบรางวัลที่ 1 ในหน้ากับที่อ่านได้จากหน้าสรุปของ Sanook
    ถ้าไม่ตรงจะลองแหล่งถัดไป และถ้ายังไม่ตรงจะไม่บันทึกงวดนั้น"""
    LAST_PRIZES.update(enabled=True, total=0, new=0, failed=0, mismatch=0, odd=0, error="",
                       nodate=0, noparse=0, http=0, by_source={s_: 0 for s_ in PRIZE_SOURCES})
    san = _cache_draws(load_cache())
    cache = {} if fresh else load_prizes_cache()
    todo = [k for k in sorted(san, reverse=True) if k not in cache]
    if todo and os.path.exists(PRIZES_DEBUG_FILE):
        os.remove(PRIZES_DEBUG_FILE)   # เริ่มตัวอย่างใหม่ทุกรอบ ไม่ให้ไฟล์โตเรื่อย ๆ
    state = {"abort": False, "dead": {}, "debug": {},
             "src": {s_: {"errors": 0, "ok": 0, "last": ""} for s_ in PRIZE_SOURCES}}
    if progress:
        progress(0, len(todo))

    def work(k):
        if state["abort"]:
            return k, "skip", None, None
        d = date(int(k[:4]), int(k[4:6]), int(k[6:]))
        time.sleep(PRIZE_DELAY)
        mismatch, last_reason = None, "http"
        for src in PRIZE_SOURCES:
            if state["dead"].get(src):
                continue
            status, got, reason, text = _try_source(src, d)
            st = state["src"][src]
            if status == "error":
                with _LOCK:
                    st["errors"] += 1
                    st["last"] = text
                    if st["ok"] == 0 and st["errors"] >= PRIZE_MAX_ERRORS:
                        state["dead"][src] = True
                        if all(state["dead"].get(x) for x in PRIZE_SOURCES):
                            state["abort"] = True
                continue
            with _LOCK:
                st["errors"] = 0
                st["ok"] += 1
            if status == "miss":
                continue
            if got is None:
                last_reason = reason
                with _LOCK:
                    n = state["debug"].get((src, reason), 0)
                    state["debug"][(src, reason)] = n + 1
                if n < 2:
                    _save_prize_debug(d, reason, text, src)
                continue
            if got["f"] != san[k]:
                mismatch = (src, got["f"])
                continue
            return k, "ok", got, src
        if mismatch:
            return k, "mismatch", mismatch, None
        return k, ("skip" if state["abort"] else last_reason), None, None

    done = 0
    if todo:
        with ThreadPoolExecutor(max_workers=PRIZE_WORKERS) as ex:
            for fut in as_completed([ex.submit(work, k) for k in todo]):
                k, kind, got, src = fut.result()
                done += 1
                d = date(int(k[:4]), int(k[4:6]), int(k[6:]))
                if kind == "ok":
                    cache[k] = got
                    LAST_PRIZES["new"] += 1
                    LAST_PRIZES["by_source"][src] += 1
                    if len(got["f3"]) != 2 or len(got["b3"]) != 2:
                        LAST_PRIZES["odd"] += 1
                elif kind == "mismatch":
                    LAST_PRIZES["mismatch"] += 1
                    LAST_WARNINGS.append(
                        f"งวด {thai_date(d)}: รางวัลที่ 1 จากหน้าสรุป Sanook = {san[k]} แต่หน้า {got[0]} ได้ {got[1]} ไม่ตรงกัน จึงไม่บันทึกรางวัลอื่นของงวดนี้"
                    )
                else:
                    LAST_PRIZES["failed"] += 1
                    LAST_PRIZES[kind if kind in ("nodate", "noparse") else "http"] += 1
                if progress and done % 5 == 0:
                    progress(done, len(todo))
                if done % 40 == 0:
                    save_prizes_cache(cache)
        if progress:
            progress(len(todo), len(todo))
        save_prizes_cache(cache)
    names = {"pptv": "PPTVHD36", "sanook": "Sanook"}
    if state["abort"]:
        why = " · ".join(f"{names[x]}: {state['src'][x]['last'][:60]}" for x in PRIZE_SOURCES)
        LAST_PRIZES["error"] = f"เปิดหน้ารายงวดไม่ได้ทั้งสองแหล่ง ({why})"
    elif todo and LAST_PRIZES["new"] == 0 and LAST_PRIZES["failed"] and not LAST_PRIZES["mismatch"]:
        if LAST_PRIZES["nodate"] >= LAST_PRIZES["noparse"]:
            LAST_PRIZES["error"] = "เปิดหน้ารายงวดได้ แต่ไม่พบวันที่ของงวดในหน้า (ดูตัวอย่างใน lottery_prize_debug.txt และท้าย lottery_verify_report.txt)"
        else:
            LAST_PRIZES["error"] = "เปิดหน้ารายงวดได้ แต่อ่านเลขหน้า/ท้าย 3 ตัวและท้าย 2 ตัวไม่ได้ (ดูตัวอย่างใน lottery_prize_debug.txt และท้าย lottery_verify_report.txt)"
    LAST_PRIZES["total"] = len(cache)
    return LAST_PRIZES


def append_prizes_report():
    """ต่อท้ายรายงานด้วยสรุปรางวัลอื่น (และตัวอย่างหน้าที่อ่านไม่ได้) เพื่อให้เปิดดูใน repository ได้โดยไม่ต้องเปิด log"""
    P = LAST_PRIZES
    lines = ["", "[5] รางวัลอื่น (เลขหน้า 3 ตัว / เลขท้าย 3 ตัว / เลขท้าย 2 ตัว)",
             f"    มีข้อมูลในแคช {P['total']} งวด ดึงใหม่รอบนี้ {P['new']} งวด",
             f"    อ่านไม่ได้ {P['failed']} งวด (ไม่พบวันที่ในหน้า {P['nodate']} · พบวันที่แต่อ่านเลขไม่ได้ {P['noparse']} · เปิดหน้าไม่ได้ {P['http']})",
             f"    รางวัลที่ 1 ไม่ตรงกับหน้าสรุป {P['mismatch']} งวด · รูปแบบแปลก (ไม่ใช่ 2/2/1 ตัว) {P['odd']} งวด",
             "    แหล่งที่ใช้รอบนี้: " + " · ".join(f"{ {'pptv': 'PPTVHD36', 'sanook': 'Sanook'}.get(k, k)} {v} งวด" for k, v in P.get("by_source", {}).items())]
    if P["error"]:
        lines.append(f"    ⚠ {P['error']}")
    try:
        if os.path.exists(PRIZES_DEBUG_FILE):
            with open(PRIZES_DEBUG_FILE, "r", encoding="utf-8") as f:
                dbg = f.read()[:3500]
            lines += ["", "    --- ตัวอย่างหน้าที่อ่านไม่ได้ (ส่งส่วนนี้ให้ผู้พัฒนาเพื่อปรับตัวอ่าน) ---", dbg]
        with open(REPORT_FILE, "a", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
    except OSError:
        pass


def write_prizes_csv(filename=None):
    """เขียน lottery_all_prizes.csv เรียงงวดใหม่สุดไว้บนสุด คืนจำนวนแถวที่มีรางวัลอื่นครบ"""
    filename = filename or PRIZES_CSV_FILE
    cache = load_prizes_cache()
    lines, full = ["date,first,front3,back3,last2"], 0
    for d, n in draws_newest_first():
        p = cache.get(f"{d:%Y%m%d}")
        if p and p["f"] == n:
            lines.append(f"{d:%Y-%m-%d},{n},{' '.join(p['f3'])},{' '.join(p['b3'])},{p['l2']}")
            full += 1
        else:
            lines.append(f"{d:%Y-%m-%d},{n},,,")
    if full:
        with open(filename, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
    return full


def read_history(filename=None):
    filename = filename or HISTORY_FILE
    if not os.path.exists(filename):
        return []
    with open(filename, "r", encoding="utf-8") as f:
        return [l.strip() for l in f if re.fullmatch(r"\d{6}", l.strip())]


def write_history(numbers, filename=None):
    filename = filename or HISTORY_FILE
    with open(filename, "w", encoding="utf-8") as f:
        f.write("\n".join(numbers) + ("\n" if numbers else ""))


def _cache_draws(cache):
    return {k: v for k, v in cache.items() if re.fullmatch(r"\d{8}", k)}


def draws_newest_first(include_glo=True):
    """[(date, เลข)] เรียงใหม่->เก่า รวมงวดของ Sanook กับงวดที่มีเฉพาะใน GLO (ถ้าเลขขัดแย้งใช้ของ Sanook)"""
    merged = _cache_draws(load_cache())
    if include_glo and USE_GLO:
        for k, v in _cache_draws(load_glo_cache()).items():
            merged.setdefault(k, v)
    out = [(date(int(k[:4]), int(k[4:6]), int(k[6:])), v) for k, v in merged.items()]
    return sorted(out, key=lambda x: x[0], reverse=True)


def plan_history(draws, current):
    """เทียบไฟล์กับ Sanook (นับตามจำนวนครั้ง) คืน (matched, missing, extras)
    matched/missing = [(date, เลข)] ; extras = เลขในไฟล์ที่ไม่มีใน Sanook (คงลำดับเดิม)"""
    left = Counter(current)
    matched, missing = [], []
    for d, n in draws:
        if left[n] > 0:
            left[n] -= 1
            matched.append((d, n))
        else:
            missing.append((d, n))
    extras = []
    for n in current:
        if left[n] > 0:
            left[n] -= 1
            extras.append(n)
    return matched, missing, extras


def sync_history(filename=None, dry_run=False, complete=None):
    """จัดไฟล์ประวัติให้งวดใหม่สุดอยู่บนสุด และเทียบกับ Sanook
      - อ่านครบทุกหน้า : ไฟล์ = ทุกงวดของ Sanook (ใหม่->เก่า) + เลขที่ Sanook ไม่มี (ต่อท้าย)
      - อ่านไม่ครบ     : ไม่เรียงทั้งไฟล์ เพียงเติมงวดที่ขาดไว้บนสุด
    คืน dict รายงาน (None ถ้ายังไม่มีข้อมูลจาก Sanook)"""
    filename = filename or HISTORY_FILE
    if complete is None:
        complete = bool(load_cache().get("_complete"))
    draws = draws_newest_first(include_glo=complete)   # อ่าน Sanook ไม่ครบ -> ไม่เอางวดเก่าจาก GLO มาปน
    if not draws:
        return None
    current = read_history(filename)
    matched, missing, extras = plan_history(draws, current)
    if complete:
        new = [n for _, n in draws] + extras
    else:
        new = [n for _, n in missing] + current
    sk_keys = set(_cache_draws(load_cache()))
    glo_only = [(d, n) for d, n in draws if f"{d:%Y%m%d}" not in sk_keys]
    changed = new != current
    report = {
        "sanook": len(draws), "matched": len(matched), "missing": missing, "extras": extras,
        "complete": complete, "added": len(missing), "reordered": complete and changed,
        "changed": changed, "written": False, "backup": False,
        "newest": draws[0][1], "newest_date": draws[0][0],
        "glo_only": len(glo_only), "glo_conflicts": glo_conflicts() if complete else [],
    }
    if changed and not dry_run:
        if current and not os.path.exists(BACKUP_FILE):
            write_history(current, BACKUP_FILE)
            report["backup"] = True
        write_history(new, filename)
        report["written"] = True
    if not dry_run:
        write_report(report, filename)
    return report


def write_report(r, filename):
    lines = [
        f"รายงานเทียบประวัติกับ Sanook  ({datetime.now():%Y-%m-%d %H:%M})",
        f"ไฟล์: {filename}",
        f"จำนวนงวดที่ Sanook มี: {r['sanook']}   ตรงกับในไฟล์: {r['matched']}",
        f"อ่านหน้าสรุปย้อนหลังครบทุกหน้า: {'ใช่' if r['complete'] else 'ไม่ครบ (จึงไม่ได้เรียงทั้งไฟล์ และไม่ได้ตรวจเลขส่วนเกิน)'}",
        "",
        f"[1] งวดที่ Sanook มีแต่ในไฟล์ไม่มี ({len(r['missing'])} งวด) -> เติมไว้บนสุดให้แล้ว",
    ]
    lines += [f"    {thai_date(d)}  {n}" for d, n in r["missing"]] or ["    (ไม่มี)"]
    lines += ["", f"[2] เลขในไฟล์ที่ไม่พบใน Sanook ({len(r['extras'])} ตัว) -> ย้ายไปท้ายไฟล์ ควรตรวจเอง"
              + ("" if r["complete"] else " (ยังไม่ได้ตรวจ)")]
    lines += [f"    {n}" for n in r["extras"]] or ["    (ไม่มี)"]
    lines += ["", f"[3] งวดที่มีเฉพาะใน GLO (เก่ากว่า Sanook) เพิ่มเข้าไฟล์แล้ว: {r.get('glo_only', 0)} งวด"]
    lines += ["", f"[4] งวดที่ Sanook กับ GLO ได้เลขไม่ตรงกัน ({len(r.get('glo_conflicts', []))} งวด) -> ในไฟล์ใช้เลขของ Sanook"]
    lines += [f"    {thai_date(d)}  Sanook={sn}  GLO={gl}" for d, sn, gl in r.get("glo_conflicts", [])] or ["    (ไม่มี)"]
    try:
        with open(REPORT_FILE, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
    except OSError:
        pass


def add_numbers_top(new_numbers, filename=None):
    """เพิ่มเลขใหม่ไว้บนสุดของไฟล์ (บรรทัดแรกของที่ส่งมา = ใหม่สุด) ข้ามเลขที่มีอยู่แล้ว คืนจำนวนที่เพิ่ม"""
    current = read_history(filename)
    have, fresh = set(current), []
    for n in new_numbers:
        n = str(n).strip()
        if re.fullmatch(r"\d{6}", n) and n not in have:
            have.add(n)
            fresh.append(n)
    if fresh:
        write_history(fresh + current, filename)
    return len(fresh)


def append_to_history(new_number, filename=None):
    """คงชื่อเดิมไว้ให้เข้ากันได้: เพิ่มไว้บนสุด (ไม่ใช่ท้ายไฟล์แล้ว)"""
    return add_numbers_top([new_number], filename) > 0


def print_report(r):
    print(f"Sanook มี {r['sanook']} งวด ตรงกับในไฟล์ {r['matched']} งวด (งวดล่าสุด {thai_date(r['newest_date'])} = {r['newest']})")
    print(f"- งวดที่ไฟล์ขาด: {len(r['missing'])}")
    for d, n in r["missing"][:20]:
        print(f"    {thai_date(d)}  {n}")
    if len(r["missing"]) > 20:
        print(f"    ... และอีก {len(r['missing']) - 20} งวด")
    print(f"- งวดเก่าที่เติมจาก GLO: {r.get('glo_only', 0)}   งวดที่ Sanook/GLO ไม่ตรงกัน: {len(r.get('glo_conflicts', []))}")
    for d, sn, gl in r.get("glo_conflicts", [])[:20]:
        print(f"    {thai_date(d)}  Sanook={sn}  GLO={gl}")
    print(f"- เลขในไฟล์ที่ไม่พบใน Sanook/GLO: {len(r['extras'])}" + ("" if r["complete"] else "  (อ่านไม่ครบ จึงยังไม่ตรวจ)"))
    for n in r["extras"][:20]:
        print(f"    {n}")


if __name__ == "__main__":
    verify_only = "--verify" in sys.argv
    print("กำลังดึงผลรางวัลที่ 1 ทุกงวดจาก Sanook (ครั้งแรกอาจใช้เวลาประมาณ 1 นาที)...")
    get_all_lotteries(lambda d, t: print(f"\r  อ่านหน้าที่ {d}", end=""))
    print()
    if USE_GLO:
        print("กำลังเติมงวดเก่าและเทียบกับ GLO (API ทางการ)...")
        extend_with_glo(lambda n, t: print(f"\r  พบงวดเก่าจาก GLO {n} งวด", end=""), verify_all="--glo-verify-all" in sys.argv)
        print()
        if LAST_GLO["error"]:
            print("⚠ GLO:", LAST_GLO["error"])
    rep_ = sync_history(dry_run=verify_only)
    if not rep_:
        print("ยังไม่มีข้อมูลจาก Sanook")
        for e in LAST_ERRORS:
            print("✗", e)
        sys.exit(1)   # ให้ GitHub Actions แสดงว่าล้มเหลว (จะได้อีเมลแจ้ง) แทนที่จะผ่านแบบเงียบ ๆ
    else:
        print_report(rep_)
        if verify_only:
            print("(โหมด --verify: ยังไม่ได้แก้ไฟล์ประวัติ)")
        elif rep_["written"]:
            print("เรียงไฟล์ให้งวดใหม่สุดอยู่บนสุดแล้ว" + (f" (สำรองไฟล์เดิมไว้ที่ {BACKUP_FILE})" if rep_["backup"] else ""))
            print(f"รายงานละเอียด: {REPORT_FILE}")
        else:
            print("ไฟล์ประวัติเรียงถูกต้องและครบอยู่แล้ว ไม่ต้องแก้")
    if USE_PRIZES and "--no-prizes" not in sys.argv:
        print("กำลังดึงเลขหน้า 3 ตัว / เลขท้าย 3 ตัว / เลขท้าย 2 ตัว (ครั้งแรกอาจใช้เวลาประมาณ 2-5 นาที)...")
        update_prizes(lambda n, t: print(f"\r  {n}/{t} งวด", end="") if t else None)
        print()
        if not verify_only:
            rows = write_prizes_csv()
            append_prizes_report()
            print(f"รางวัลอื่นครบ {rows} งวด (ใหม่ {LAST_PRIZES['new']} · ข้าม/อ่านไม่ได้ {LAST_PRIZES['failed']}) -> {PRIZES_CSV_FILE}")
        if LAST_PRIZES["error"]:
            print("⚠", LAST_PRIZES["error"])
    for w in LAST_WARNINGS:
        print("⚠", w)
    for e in LAST_ERRORS:
        print("✗", e)
