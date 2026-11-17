"""
QR Studio - desktop + Android (Kivy)
====================================
Clean, engraving-ready QR codes: PNG for print, SVG for laser / CNC.

Four modes
  * Single link : one platform link -> one QR code.
  * All in one  : a links / business-card page -> one QR code (and NFC tag).
                  Stored on GitHub (editable after engraving) or inside the link.
  * Menu        : restaurant / shop menu page (Arabic + English), editable after engraving.
  * Offline     : text, serial numbers, vCard, WiFi, location, phone, SMS, email, product data
                  placed directly inside the code. No internet needed to scan it.

Arabic        : fields accept Arabic (pip install arabic-reshaper python-bidi, plus an Arabic .ttf in ./fonts).
Desktop dependencies : pip install kivy qrcode pillow certifi arabic-reshaper python-bidi
Android              : see README_SETUP.txt (buildozer requirements)
"""

import base64
import copy
import hashlib
import io
import json
import math
import os
import re
import secrets
import string
import subprocess
import threading
import time
import urllib.error
import urllib.request
import zlib
from urllib.parse import quote

import qrcode
from PIL import Image, ImageDraw

from kivy.utils import platform
from kivy.config import Config

if platform in ("win", "linux", "macosx"):
    Config.set("input", "mouse", "mouse,multitouch_on_demand")

from kivy.app import App  # noqa: E402  (Config must be set before the window is created)
from kivy.clock import Clock  # noqa: E402
from kivy.core.clipboard import Clipboard  # noqa: E402
from kivy.core.window import Window  # noqa: E402
from kivy.graphics import Color, RoundedRectangle  # noqa: E402
from kivy.metrics import dp  # noqa: E402
from kivy.properties import StringProperty  # noqa: E402
from kivy.uix.behaviors import ButtonBehavior  # noqa: E402
from kivy.uix.boxlayout import BoxLayout  # noqa: E402
from kivy.uix.button import Button  # noqa: E402
from kivy.uix.dropdown import DropDown  # noqa: E402
from kivy.uix.filechooser import FileChooserListView  # noqa: E402
from kivy.uix.floatlayout import FloatLayout  # noqa: E402
from kivy.uix.gridlayout import GridLayout  # noqa: E402
from kivy.uix.image import Image as KivyImage  # noqa: E402
from kivy.uix.label import Label  # noqa: E402
from kivy.uix.popup import Popup  # noqa: E402
from kivy.uix.scrollview import ScrollView  # noqa: E402
from kivy.uix.slider import Slider  # noqa: E402
from kivy.uix.textinput import TextInput  # noqa: E402
from kivy.uix.widget import Widget  # noqa: E402

IS_ANDROID = platform == "android"
IS_MOBILE = platform in ("android", "ios")
RESAMPLE = getattr(Image, "Resampling", Image).LANCZOS


# =============================================================================
# CONFIGURATION
# =============================================================================

# --- Link shortener -----------------------------------------------------------
# is.gd needs no account and no API key.
# Limits (per IP): 200 new short links per hour. Links are permanent and cannot be edited.
SHORTENER_API = "https://is.gd/create.php"
SHORTENER_NAME = "is.gd"

# --- Paths --------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOGO_FOLDER = os.path.join(BASE_DIR, "logo_qr")  # platform logos shipped with the app

# --- QR rendering -------------------------------------------------------------
BOX_SIZE = 40  # pixels per module in the PNG
BORDER_MODULES = 4  # quiet zone in the PNG (modules)
MAX_VERSION = 3  # 29x29 modules max, anything bigger is refused
OFFLINE_MAX_VERSION = 10  # offline codes carry their data, so they may be denser (57x57)
MIN_MODULE_MM = 0.5  # smaller squares are hard to engrave / scan
AUTO_DIRECT_MAX_VERSION = 2  # "Auto" uses the direct link if it fits 25x25 or smaller
CENTER_LOGO_RATIO = 0.15  # center logo width, relative to the data area
CENTER_LOGO_MAX_RATIO = 0.25  # most of the data area the logo may hide

# --- Links page (All in one) --------------------------------------------------
ALL_KEY = "All in One"
GH_USER = "fennecsys"
REPO_PAGES = "c"  # engine (index.html) + items/<id>.json + index.json
REPO_ASSETS = "a"  # images: logos, backgrounds, dishes
REPO_TEMPLATES = "t"  # shared design templates
DEFAULT_GITHUB = f"https://{GH_USER}.github.io/{REPO_PAGES}/"
OLD_DEFAULT_GITHUB = "https://sidoubens.github.io/my-qr-links/"
ITEMS_FOLDER = "items"  # in the pages repository: one file per card / menu
INDEX_FILE = "index.json"
ASSET_IMG_FOLDER = "img"  # in the assets repository
ITEM_ID_LEN = 8
LOGO_UPLOAD_FOLDER = "logos"  # folder inside the GitHub Pages repository (old in-link mode)
LOGO_UPLOAD_PX = 256  # page logos are shrunk to this size before upload
BG_UPLOAD_PX = 1280  # background pictures
DISH_UPLOAD_PX = 480  # menu photos
STORE_LINK = "In link"
STORE_GITHUB = "GitHub (editable)"
STORES = [STORE_LINK, STORE_GITHUB]
LANG_CHOICES = {"Auto": "", "Arabic": "ar", "English": "en"}

# --- App defaults -------------------------------------------------------------
DEFAULT_SIZE_MM = 40.0
DEFAULT_PLATFORM = "Instagram"
NARROW_WIDTH_DP = 720  # below this width the app uses the single-column layout

MODE_SINGLE = "single"
MODE_ALL = "all"
MODE_MENU = "menu"
MODE_OFFLINE = "offline"
MODE_LABELS = {MODE_SINGLE: "Single link", MODE_ALL: "All in one", MODE_MENU: "Menu", MODE_OFFLINE: "Offline"}
LABEL_TO_MODE = {label: mode for mode, label in MODE_LABELS.items()}

LINK_TYPES = ["Auto", "Direct", "Short"]
LOGO_CHOICES = ["No logo", "B&W logo", "Color logo"]

# --- Texts --------------------------------------------------------------------
LINK_HINTS = {
    "Auto": "Opens the app straight from the scanner when the link is short enough, otherwise shortens it.",
    "Direct": "The scanner opens the app directly. The code can get bigger for long links.",
    "Short": "Fewest squares. The phone may open the browser before the app.",
}
ROUTE_TEXT = {
    "direct": "Direct link: scanning opens the app right away.",
    "short": "Short link: fewest squares. The browser may open before the app.",
    "fallback": "Shortener unreachable, so the direct link was used.",
    "page": "Opens your links page. Each icon opens its app.",
    "item": "Short fixed link. You can change the page later from the app: the code and the NFC tag stay the same.",
    "offline": "Offline code: the data is inside the code. It works without internet and cannot be changed.",
    "contact": "Scanning opens the mail app or the phone dialer directly.",
}
FIELD_HINTS = {"Email": ("EMAIL ADDRESS", "name@example.com"), "Phone": ("PHONE NUMBER", "+213 555 12 34 56")}
DEFAULT_FIELD_HINT = "@username or full link"
MULTI_FIELD_HINT = "@username or link"  # All-in-one fields

# --- Platforms ----------------------------------------------------------------
# Display name -> short id (also the logo file prefix and the id used by the links page).
PLATFORMS = {
    "Facebook": "f",
    "Discord": "d",
    "Instagram": "i",
    "LinkedIn": "l",
    "Localisation": "lc",
    "Pinterest": "p",
    "Snapchat": "s",
    "TikTok": "t",
    "Telegram": "tl",
    "WhatsApp": "w",
    "Web Page": "wb",
    "X": "x",
    "YouTube": "y",
    "Email": "e",
    "Phone": "tp",
}
PLATFORM_PREFIX = dict(PLATFORMS)
PLATFORM_PREFIX[ALL_KEY] = "a"

USER_TEMPLATES = {
    "Facebook": "facebook.com/{}",
    "Instagram": "instagram.com/{}",
    "LinkedIn": "linkedin.com/in/{}",
    "Pinterest": "pinterest.com/{}",
    "Snapchat": "snapchat.com/add/{}",
    "TikTok": "tiktok.com/@{}",
    "Telegram": "t.me/{}",
    "X": "x.com/{}",
    "YouTube": "youtube.com/@{}",
    "Discord": "discord.gg/{}",
}

CONTACT_SCHEMES = ("mailto:", "tel:")  # opened by the mail app / dialer, never shortened


# =============================================================================
# DESIGN TOKENS
# =============================================================================
def rgba(hex_color, alpha=1.0):
    """'#RRGGBB' -> (r, g, b, a) with components in 0..1."""
    h = hex_color.lstrip("#")
    return (int(h[0:2], 16) / 255.0, int(h[2:4], 16) / 255.0, int(h[4:6], 16) / 255.0, alpha)


BG = rgba("#0A0F1E")
SURFACE = rgba("#111830")
SURFACE2 = rgba("#19234A")
FIELD = rgba("#0D1429")
BORDER = rgba("#26335C")
ACCENT = rgba("#4F8CFF")
ACCENT_SOFT = rgba("#1B2C55")
TEXT = rgba("#EAF0FF")
MUTED = rgba("#8C99BD")
SUCCESS = rgba("#38D39F")
ERROR = rgba("#FF6B6B")


# =============================================================================
# ARABIC SUPPORT
# Kivy draws letters one by one: Arabic needs shaping (letters joined) and reordering (right to left)
# before it is drawn, and a font that contains the Arabic letters.
#   pip install arabic-reshaper python-bidi      + an Arabic font in ./fonts (Cairo, Amiri, Noto Naskh...)
# The real (logical) text is what gets saved and uploaded; the shaped text is only what is drawn.
# =============================================================================
try:
    import arabic_reshaper

    try:
        from bidi.algorithm import get_display  # python-bidi 0.4.x (pure Python, use this one for Android)
    except ImportError:
        from bidi import get_display  # python-bidi 0.5+

    HAS_ARABIC = True
except Exception:  # the app still works; Arabic is then shown unshaped
    arabic_reshaper = None
    get_display = None
    HAS_ARABIC = False

ARABIC_RE = re.compile("[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]")


def has_arabic(text):
    return bool(text) and bool(ARABIC_RE.search(text))


def shape(text):
    """Logical text -> text ready to be drawn by Kivy (joined letters, visual order). Latin text is unchanged."""
    if not HAS_ARABIC or not has_arabic(text):
        return text
    try:
        return "\n".join(get_display(arabic_reshaper.reshape(line)) for line in text.split("\n"))
    except Exception:
        return text


def find_arabic_font():
    """First Arabic-capable font found: ./fonts first, then common system fonts. '' when none."""
    base = os.path.dirname(os.path.abspath(__file__))
    candidates = []
    fonts_dir = os.path.join(base, "fonts")
    if os.path.isdir(fonts_dir):
        names = sorted(f for f in os.listdir(fonts_dir) if f.lower().endswith((".ttf", ".otf")))
        preferred = [n for n in names if n.lower().startswith(("cairo", "amiri", "noto", "tajawal"))]
        candidates += [os.path.join(fonts_dir, n) for n in preferred + [n for n in names if n not in preferred]]
    candidates += [
        "/system/fonts/NotoNaskhArabic-Regular.ttf",
        "/system/fonts/NotoSansArabic-Regular.ttf",
        "/system/fonts/DroidSansArabic.ttf",
        "C:/Windows/Fonts/tahoma.ttf",
        "C:/Windows/Fonts/segoeui.ttf",
        "C:/Windows/Fonts/arial.ttf",
        "/Library/Fonts/Arial Unicode.ttf",
        "/usr/share/fonts/truetype/noto/NotoSansArabic-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    for path in candidates:
        if os.path.isfile(path):
            return path
    return ""


AR_FONT = find_arabic_font()


# =============================================================================
# STORAGE / PLATFORM HELPERS
# =============================================================================
def _writable(folder):
    """True when `folder` exists (or can be created) and a file can be written in it."""
    try:
        os.makedirs(folder, exist_ok=True)
        probe = os.path.join(folder, ".write_test")
        with open(probe, "w") as f:
            f.write("x")
        os.remove(probe)
        return True
    except Exception:
        return False


def request_android_permissions():
    if not IS_ANDROID:
        return
    try:
        from android.permissions import request_permissions, Permission

        request_permissions([Permission.WRITE_EXTERNAL_STORAGE, Permission.READ_EXTERNAL_STORAGE])
    except Exception as e:
        print(f"[Permissions] {e}")


def get_save_folder(user_dir):
    """First writable folder wins. Android: public Download first so files show in the file manager."""
    if IS_ANDROID:
        candidates = [
            "/storage/emulated/0/Download/QR_Codes",
            "/sdcard/Download/QR_Codes",
            "/storage/emulated/0/Documents/QR_Codes",
            "/storage/emulated/0/Pictures/QR_Codes",
            os.path.join(user_dir, "QR_Codes"),
        ]
    else:
        candidates = [
            os.path.join(os.path.expanduser("~"), "Downloads", "QR_Codes"),
            os.path.join(user_dir, "QR_Codes"),
        ]
    for folder in candidates:
        if _writable(folder):
            return folder
    return user_dir


def export_to_shared(path):
    """Android: copies a private file into shared storage so the gallery / file manager sees it."""
    if not IS_ANDROID:
        return False
    try:
        from androidstorage4kivy import SharedStorage

        SharedStorage().copy_to_shared(path)
        return True
    except Exception as e:
        print(f"[Share] copy_to_shared failed: {e}")
        return False


def share_file(path):
    try:
        from androidstorage4kivy import ShareSheet

        ShareSheet().share_file(path)
        return True
    except Exception as e:
        print(f"[Share] share_file failed: {e}")
        return False


def open_folder(path):
    try:
        if platform == "win":
            os.startfile(path)
        elif platform == "macosx":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
        return True
    except Exception as e:
        print(f"[Folder] {e}")
        return False


def _ssl_context():
    """SSL context backed by certifi (needed on Android); None falls back to the system default."""
    try:
        import ssl

        import certifi

        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return None


# =============================================================================
# LINK SHORTENER
# =============================================================================
def _read_shortener_answer(request):
    """Sends the request and returns the raw body.
    is.gd explains its errors in a JSON body, so an HTTP error with a body is still returned."""
    try:
        with urllib.request.urlopen(request, timeout=10, context=_ssl_context()) as response:
            return response.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", "replace")
        except Exception:
            body = ""
        if not body.strip():
            print(f"[API Error] {SHORTENER_NAME} HTTP {e.code}")
            raise ValueError(f"{SHORTENER_NAME} error (HTTP {e.code}). Try again in a minute.")
        return body
    except Exception as e:
        print(f"[API Error] Shortening failed: {e}")
        raise ValueError("URL shortening failed. Check your internet connection.")


def shorten_url(long_url):
    """Shortens a URL with is.gd (free, no API key). Raises ValueError on failure.
    The long URL is fully percent-encoded, so '#', '&', '+' inside it are kept intact."""
    if not long_url.lower().startswith(("http://", "https://")):
        long_url = "https://" + long_url

    request = urllib.request.Request(
        SHORTENER_API + "?format=json&url=" + quote(long_url, safe=""),
        headers={"Accept": "application/json", "User-Agent": "Mozilla/5.0 (QR-Studio)"},
        method="GET",
    )
    body = _read_shortener_answer(request)

    try:
        result = json.loads(body)
        if not isinstance(result, dict):
            raise ValueError("not an object")
    except ValueError:
        print(f"[API Error] Unexpected answer: {body[:200]}")
        raise ValueError(f"URL shortening failed: unexpected answer from {SHORTENER_NAME}.")

    short = result.get("shorturl")
    if short:
        return short

    code = result.get("errorcode")
    message = result.get("errormessage", "")
    print(f"[API Error] {SHORTENER_NAME} code={code}: {message}")
    if code == 3:
        raise ValueError(
            f"{SHORTENER_NAME} rate limit reached (about 200 links per hour). Wait a few minutes and try again."
        )
    if code == 1:
        raise ValueError(f"{SHORTENER_NAME} refused this link: {message}")
    raise ValueError(f"{SHORTENER_NAME} is unavailable right now. Try again later.")


# =============================================================================
# LINK BUILDING
# =============================================================================
def _email_link(text):
    address = re.sub(r"^mailto:", "", text, flags=re.IGNORECASE).strip()
    if not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", address):
        raise ValueError("Enter a valid email address.")
    return "mailto:" + address


def _phone_link(text):
    raw = re.sub(r"^tel:", "", text, flags=re.IGNORECASE).strip()
    digits = re.sub(r"\D", "", raw)
    if digits.startswith("00"):
        digits = digits[2:]
    elif digits.startswith("0") and not raw.startswith("+"):
        raise ValueError("Use the international phone format (e.g. +213...).")
    if len(digits) < 6:
        raise ValueError("Enter a valid phone number.")
    return "tel:+" + digits


def _whatsapp_link(text):
    if "wa.me" in text:
        return text
    digits = re.sub(r"\D", "", text)
    if digits.startswith("00"):
        digits = digits[2:]
    elif digits.startswith("0"):
        raise ValueError("Use the international phone format (e.g. 213...).")
    return "wa.me/" + digits


def _location_link(text):
    coords = re.match(r"^\s*(-?\d+(?:\.\d+)?)\s*[,; ]\s*(-?\d+(?:\.\d+)?)\s*$", text)
    if coords:
        return "google.com/maps?q={},{}".format(coords.group(1), coords.group(2))
    if "." in text:
        return text
    raise ValueError("Enter coordinates or a map link.")


def _username_link(platform_name, text):
    user = text.lstrip("@").strip("/")
    if not user or re.search(r"\s", user):
        raise ValueError("Invalid username.")
    return USER_TEMPLATES[platform_name].format(quote(user, safe="._-"))


def build_link(platform_name, text):
    """Builds the plain link for a platform from a username or a pasted link.
    Web links come back without a scheme; email and phone keep 'mailto:' / 'tel:'."""
    text = text.strip()

    if platform_name == "Email":
        return _email_link(text)
    if platform_name == "Phone":
        return _phone_link(text)

    text = re.sub(r"^https?://(www\.)?", "", text, flags=re.IGNORECASE)

    if platform_name == "WhatsApp":
        return _whatsapp_link(text)
    if platform_name == "Localisation":
        return _location_link(text)
    if platform_name in USER_TEMPLATES:
        return _username_link(platform_name, text)
    if "." in text or "/" in text:
        return text
    raise ValueError("Enter a valid link.")


def _escape_field(value):
    """';' and '|' separate fields on the links page, so they are percent-encoded inside a value."""
    return value.replace(";", "%3B").replace("|", "%7C")


def encode_links(name, items, logo_id=None):
    """Data placed after the '#' of the links page: name|id:link;id:link|logoId, deflated and base64url.
    The logo itself is never inside the link, only its short id."""
    links = ";".join(f"{pid}:{_escape_field(val)}" for pid, val in items)
    text = f"{name.replace('|', ' ')}|{links}" + (f"|{logo_id}" if logo_id else "")
    compressor = zlib.compressobj(9, zlib.DEFLATED, -15)
    packed = compressor.compress(text.encode("utf-8")) + compressor.flush()
    return base64.urlsafe_b64encode(packed).decode("ascii").rstrip("=")


# =============================================================================
# PAGE LOGO UPLOAD (GitHub)
# =============================================================================
def derive_repo(pages_url):
    """https://owner.github.io/repo/ -> 'owner/repo' ('' when it is not a github.io address)."""
    m = re.match(r"https?://([^./]+)\.github\.io/([^/#?]+)", pages_url.strip())
    return f"{m.group(1)}/{m.group(2)}" if m else ""


def prepare_logo(path):
    """Shrinks the chosen image to a small PNG. Returns (short id from the content, png bytes).
    The same picture always gives the same id, so it is uploaded only once."""
    img = Image.open(path).convert("RGBA")
    img.thumbnail((LOGO_UPLOAD_PX, LOGO_UPLOAD_PX), RESAMPLE)
    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    data = buf.getvalue()
    return hashlib.sha1(data).hexdigest()[:8], data


def _github_error_message(code, repo, what="the logo"):
    if code in (401, 403):
        return "GitHub refused the token. Check it in Settings (it needs write access to the repository contents)."
    if code == 404:
        return f"Repository {repo} not found, or the token cannot reach it."
    return f"GitHub error {code} while uploading {what}."


def github_put_file(cfg, path, data, message, overwrite=False, what="the logo"):
    """Creates <path> in the Pages repository. An existing file is left alone, or replaced when `overwrite`.
    `cfg` holds 'repo' (owner/repo) and 'token'. Raises ValueError with a readable message."""
    api = f"https://api.github.com/repos/{cfg['repo']}/contents/{path}"
    headers = {
        "Authorization": "Bearer " + cfg["token"],
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "QR-Studio",
    }
    failed = (
        "Logo upload failed. Check your internet connection."
        if what == "the logo"
        else f"Upload of {what} failed. Check your internet connection."
    )

    # 1) Already there? (a replacement needs the file's current version id)
    sha = None
    try:
        check = urllib.request.Request(api, headers=headers, method="GET")
        with urllib.request.urlopen(check, timeout=15, context=_ssl_context()) as response:
            if not overwrite:
                return
            sha = json.loads(response.read().decode("utf-8")).get("sha")
    except urllib.error.HTTPError as e:
        if e.code != 404:
            raise ValueError(_github_error_message(e.code, cfg["repo"], what))
        # 404 can also mean "no such repository"; the upload below reports that clearly
    except Exception as e:
        print(f"[GitHub] check failed: {e}")
        raise ValueError(failed)

    # 2) Upload it.
    payload = {"message": message, "content": base64.b64encode(data).decode("ascii")}
    if sha:
        payload["sha"] = sha
    try:
        upload = urllib.request.Request(
            api,
            data=json.dumps(payload).encode("utf-8"),
            headers=dict(headers, **{"Content-Type": "application/json"}),
            method="PUT",
        )
        with urllib.request.urlopen(upload, timeout=30, context=_ssl_context()):
            pass
    except urllib.error.HTTPError as e:
        raise ValueError(_github_error_message(e.code, cfg["repo"], what))
    except Exception as e:
        print(f"[GitHub] upload failed: {e}")
        raise ValueError(failed)


def github_upload_logo(cfg, logo_id, data):
    """Uploads <folder>/<id>.png (skipped when it is already there)."""
    github_put_file(cfg, f"{cfg['folder']}/{logo_id}.png", data, f"Add page logo {logo_id}")


# =============================================================================
# PAGE DESIGN (All in one)
# The design only describes APPEARANCE and is published as designs/<id>.json.
# Names, links, numbers and every text stay inside the QR link itself.
# Keep DESIGN_DEFAULTS / DESIGN_RULES identical to the ones in index.html.
# =============================================================================
DESIGN_FOLDER = "designs"  # folder inside the GitHub Pages repository
PROJECTS_FILE = "projects.json"  # saved projects + own designs, inside the app data folder
MAX_ENTRIES = 80
MAX_VALUES = 10
MAX_TEXT = 400

FONT_CHOICES = [
    "Poppins",
    "Inter",
    "Montserrat",
    "Playfair Display",
    "Lobster",
    "Cairo",
    "Tajawal",
    "Almarai",
    "Amiri",
    "Reem Kufi",
    "Changa",
]

DESIGN_DEFAULTS = {
    "bg": {
        "m": "solid",
        "c1": "#0a0f1e",
        "c2": "#1b2c55",
        "c3": "",
        "a": 160,
        "gl": 1,
        "g1": "#2563eb",
        "g2": "#9333ea",
        "g3": "#0891b2",
        "pt": "none",
        "pc": "#ffffff",
        "po": 0.08,
        "bi": "",
        "bl": 0,
        "dm": 0,
    },
    "tx": {
        "f": "Poppins",
        "ff": "",
        "c": "#eef2ff",
        "mu": "#8f9bbd",
        "tg": 1,
        "n1": "#38bdf8",
        "n2": "#818cf8",
        "n3": "#c084fc",
        "s": 30,
        "al": "c",
    },
    "av": {"sh": "c", "sz": 108, "rg": "g", "rc": "#818cf8", "ab": "#0d1328", "gw": 1},
    "cd": {
        "st": "glass",
        "r": 20,
        "cb": "",
        "bd": "",
        "sh": 1,
        "gap": 12,
        "pd": 12,
        "tl": "white",
        "ts": 54,
        "br": 1,
        "ac": "#818cf8",
        "sv": 0,
    },
    "ly": {"m": "list", "ex": "one", "cnt": 1, "lang": 1, "hint": 1},
    "x": {"css": ""},
    "e": {},
    "ft": -1,
}

# kind: c = colour, c0 = colour or empty, n = number (min, max), e = one of, b = 0/1, f = font
DESIGN_RULES = {
    "bg": {
        "m": ("e", "solid", "gradient"),
        "c1": ("c",),
        "c2": ("c",),
        "c3": ("c0",),
        "a": ("n", 0, 360),
        "gl": ("b",),
        "g1": ("c",),
        "g2": ("c",),
        "g3": ("c",),
        "pt": ("e", "none", "dots", "lines", "grid", "waves"),
        "pc": ("c",),
        "po": ("n", 0, 0.5),
        "bi": ("u",),
        "bl": ("n", 0, 40),
        "dm": ("n", 0, 0.9),
    },
    "tx": {
        "f": ("f",),
        "ff": ("ff",),
        "c": ("c",),
        "mu": ("c",),
        "tg": ("b",),
        "n1": ("c",),
        "n2": ("c",),
        "n3": ("c",),
        "s": ("n", 18, 52),
        "al": ("e", "c", "s", "e"),
    },
    "av": {
        "sh": ("e", "c", "r", "s"),
        "sz": ("n", 70, 160),
        "rg": ("e", "g", "s", "n"),
        "rc": ("c",),
        "ab": ("c",),
        "gw": ("b",),
    },
    "cd": {
        "st": ("e", "glass", "solid", "outline", "flat"),
        "r": ("n", 0, 36),
        "cb": ("c0",),
        "bd": ("c0",),
        "sh": ("b",),
        "gap": ("n", 4, 28),
        "pd": ("n", 6, 24),
        "tl": ("e", "white", "soft", "none", "round"),
        "ts": ("n", 36, 76),
        "br": ("b",),
        "ac": ("c",),
        "sv": ("b",),
    },
    "ly": {
        "m": ("e", "list", "grid", "icons"),
        "ex": ("e", "one", "many"),
        "cnt": ("b",),
        "lang": ("b",),
        "hint": ("b",),
    },
    "x": {"css": ("t", 3000)},
}

ENTRY_STYLE_RULES = {
    "ac": ("c0",),
    "cb": ("c0",),
    "tl": ("e", "", "white", "soft", "none", "round"),
    "sz": ("e", "", "f", "h"),
}

HEX_RE = re.compile(r"^#[0-9a-fA-F]{6}$")
IMG_RE = re.compile(r"^https://[a-z0-9-]+\.github\.io/[A-Za-z0-9_./-]{1,200}$", re.I)  # same rule as index.html
ITEM_ID_RE = re.compile(r"^[a-z0-9]{4,24}$")
ID_TO_NAME = {pid: name for name, pid in PLATFORMS.items()}

# Starting points for the design editor (only what differs from the defaults).
TEMPLATES = {
    "Midnight": {},
    "Light": {
        "bg": {"c1": "#f4f6fb", "gl": 0},
        "tx": {"c": "#16203a", "mu": "#5a6485", "tg": 0, "n1": "#16203a"},
        "av": {"rg": "s", "rc": "#2563eb", "ab": "#e8eefc", "gw": 0},
        "cd": {"st": "solid", "cb": "#ffffff", "bd": "#dfe4f0", "sh": 0},
    },
    "Ocean": {
        "bg": {"m": "gradient", "c1": "#031b34", "c2": "#0b5d8a", "c3": "#12a4b6", "a": 200, "pt": "waves", "po": 0.15},
        "cd": {"r": 28, "gap": 16},
    },
    "Gold": {
        "bg": {
            "m": "gradient",
            "c1": "#1a1204",
            "c2": "#3a2a08",
            "a": 135,
            "gl": 0,
            "pt": "dots",
            "pc": "#ffd166",
            "po": 0.12,
        },
        "tx": {"f": "Playfair Display", "c": "#fff6dd", "mu": "#c9b27a", "tg": 0, "n1": "#ffd166", "s": 34},
        "cd": {"st": "outline", "bd": "#b8902f", "r": 14, "br": 0, "ac": "#ffd166", "tl": "soft"},
    },
    "Forest": {
        "bg": {"c1": "#07140d", "g1": "#16a34a", "g2": "#065f46", "g3": "#84cc16"},
        "tx": {"n1": "#86efac", "n2": "#4ade80", "n3": "#a3e635"},
        "av": {"rc": "#4ade80", "ab": "#0b1f14"},
        "cd": {"ac": "#4ade80"},
    },
    "Rose": {
        "bg": {
            "m": "gradient",
            "c1": "#1f0a17",
            "c2": "#4a1230",
            "a": 150,
            "g1": "#e11d48",
            "g2": "#9d174d",
            "g3": "#f472b6",
        },
        "tx": {"n1": "#fda4af", "n2": "#f472b6", "n3": "#e879f9"},
        "cd": {"ac": "#f472b6", "r": 26},
    },
    "Mono": {
        "bg": {"c1": "#0b0b0c", "gl": 0},
        "tx": {"tg": 0, "n1": "#ffffff", "mu": "#9a9a9a", "c": "#f2f2f2"},
        "av": {"rg": "s", "rc": "#ffffff", "ab": "#161616", "gw": 0},
        "cd": {"st": "outline", "bd": "#3a3a3a", "br": 0, "ac": "#ffffff", "tl": "round", "r": 12},
        "ly": {"lang": 1},
    },
}


def _clean_value(rule, value, fallback):
    """One design value checked against its rule; anything invalid becomes `fallback`."""
    kind = rule[0]
    if kind in ("c", "c0"):
        if kind == "c0" and value == "":
            return ""
        return value.lower() if isinstance(value, str) and HEX_RE.match(value) else fallback
    if kind == "n":
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            return fallback
        value = min(rule[2], max(rule[1], value))
        return int(value) if float(value).is_integer() and not isinstance(rule[1], float) and rule[2] >= 1 else value
    if kind == "e":
        return value if value in rule[1:] else fallback
    if kind == "b":
        return int(bool(value)) if value in (0, 1, True, False) else fallback
    if kind == "f":
        return value if value in FONT_CHOICES else fallback
    if kind == "ff":  # any Google font name
        return value if isinstance(value, str) and re.match(r"^[A-Za-z0-9 ]{2,40}$", value) else ""
    if kind == "u":  # picture on a github.io address
        return value if isinstance(value, str) and IMG_RE.match(value) else ""
    if kind == "t":  # free text (custom CSS)
        return value.replace("<", "")[: rule[1]] if isinstance(value, str) else ""
    return fallback


def clean_design(raw):
    """Full design dict (defaults filled in, invalid values replaced). Never raises."""
    out = json.loads(json.dumps(DESIGN_DEFAULTS))
    if not isinstance(raw, dict):
        return out
    for group, rules in DESIGN_RULES.items():
        src = raw.get(group)
        if isinstance(src, dict):
            for key, rule in rules.items():
                out[group][key] = _clean_value(rule, src.get(key), out[group][key])
    ft = raw.get("ft")
    if isinstance(ft, int) and not isinstance(ft, bool) and 0 <= ft < MAX_ENTRIES:
        out["ft"] = ft
    styles = raw.get("e")
    if isinstance(styles, dict):
        for k, v in styles.items():
            if isinstance(k, str) and re.match(r"^\d{1,2}$", k) and isinstance(v, dict):
                out["e"][k] = {key: _clean_value(rule, v.get(key), "") for key, rule in ENTRY_STYLE_RULES.items()}
    return out


def template_design(name):
    return clean_design(TEMPLATES.get(name, {}))


def design_is_default(design):
    return clean_design(design) == clean_design(None)


def design_json(design):
    return json.dumps(clean_design(design), sort_keys=True, separators=(",", ":")).encode("utf-8")


def design_id_for(design):
    """Content-based id: the same look always gets the same file, which is uploaded only once."""
    return "d" + hashlib.sha1(design_json(design)).hexdigest()[:8]


def slugify_design_name(text):
    slug = re.sub(r"[^a-z0-9_-]+", "-", text.strip().lower()).strip("-")[:40]
    return slug or "design"


# --- entries (one per platform card or section title) ---------------------------
def new_entry(name):
    return {
        "id": PLATFORMS[name],
        "name": name,
        "values": [""],
        "labels": [""],
        "title": "",
        "text": "",
        "group": 1,
        "sv": "",
        "style": {"ac": "", "cb": "", "tl": "", "sz": ""},
        "featured": 0,
    }


def new_heading():
    return {"id": "_h", "name": "", "title": ""}


def _text(value, limit=MAX_TEXT):
    return value[:limit] if isinstance(value, str) else ""


def clean_entries(raw):
    """Entries coming from a saved project or an imported file -> safe, complete entries."""
    entries = []
    for item in (raw if isinstance(raw, list) else [])[:MAX_ENTRIES]:
        if not isinstance(item, dict):
            continue
        if item.get("id") == "_h":
            heading = new_heading()
            heading["title"] = _text(item.get("title"), 80)
            entries.append(heading)
            continue
        name = ID_TO_NAME.get(item.get("id"))
        if not name:
            continue
        entry = new_entry(name)
        values = [_text(v) for v in item.get("values", [])][:MAX_VALUES] if isinstance(item.get("values"), list) else []
        labels = [_text(v) for v in item.get("labels", [])] if isinstance(item.get("labels"), list) else []
        entry["values"] = values or [""]
        entry["labels"] = (labels + [""] * len(entry["values"]))[: len(entry["values"])]
        entry["title"] = _text(item.get("title"), 80)
        entry["text"] = _text(item.get("text"))
        entry["group"] = 0 if item.get("group") in (0, False) else 1
        entry["sv"] = item.get("sv") if item.get("sv") in ("1", "0") else ""
        style = item.get("style") if isinstance(item.get("style"), dict) else {}
        entry["style"] = {key: _clean_value(rule, style.get(key), "") for key, rule in ENTRY_STYLE_RULES.items()}
        entry["featured"] = 1 if item.get("featured") else 0
        entries.append(entry)
    return entries


def clean_texts(raw):
    raw = raw if isinstance(raw, dict) else {}
    return {
        "hint": _text(raw.get("hint")),
        "intro": _text(raw.get("intro")),
        "footer": _text(raw.get("footer")),
        "vcard": 1 if raw.get("vcard") else 0,
        "name_en": _text(raw.get("name_en"), 80),
        "hint_en": _text(raw.get("hint_en")),
        "intro_en": _text(raw.get("intro_en")),
        "footer_en": _text(raw.get("footer_en")),
        "lang": raw.get("lang") if raw.get("lang") in ("ar", "en") else "",
    }


def bi_value(ar, en):
    """Arabic + English text -> what is stored: a plain string when only one exists, else {"ar":..,"en":..}."""
    ar, en = (ar or "").strip(), (en or "").strip()
    if ar and en:
        return {"ar": ar, "en": en}
    return ar or en


def bi_parts(value):
    """Stored text -> (arabic/main, english). A plain string is the main text."""
    if isinstance(value, dict):
        return _text(value.get("ar")), _text(value.get("en"))
    return _text(value), ""


def compile_page(entries, design):
    """Entries -> (list for the page, final design).
    Empty entries are dropped, so per-entry styles and the featured card are re-keyed by the final position."""
    items, styles, featured = [], {}, -1
    for entry in entries:
        if entry["id"] == "_h":
            title = entry["title"].strip()
            if title:
                items.append({"i": "_h", "t": title})
            continue
        values, labels = [], []
        for value, label in zip(entry["values"], entry["labels"]):
            if not value.strip():
                continue
            try:
                link = build_link(entry["name"], value)
            except ValueError as e:
                raise ValueError(f"{entry['name']}: {e}")
            if link.lower().startswith(CONTACT_SCHEMES):
                link = link.split(":", 1)[1]  # the links page adds mailto:/tel: itself
            values.append(link)
            labels.append(label.strip())
        if not values:
            continue

        item = {"i": entry["id"], "v": values}
        if entry["title"].strip():
            item["t"] = entry["title"].strip()
        if entry["text"].strip():
            item["s"] = entry["text"].strip()
        if any(labels):
            item["lb"] = labels
        if entry["sv"] in ("0", "1"):
            item["sv"] = int(entry["sv"])
        if len(values) > 1 and not entry["group"]:
            item["gr"] = 0

        index = len(items)
        style = {k: v for k, v in entry["style"].items() if v}
        if style:
            styles[str(index)] = style
        if entry["featured"] and featured < 0:
            featured = index
        items.append(item)

    final = clean_design(design)
    final["e"] = clean_design({"e": styles})["e"]
    final["ft"] = featured
    return items, clean_design(final)


def build_payload(name, texts, items, logo_id=None, design_id=None, design=None, logo_url=None, item_type=None):
    """The page data (v2). `design` is placed inside the data (browser preview, and pages stored on GitHub).
    Texts may carry an English version: {"ar": .., "en": ..} (the page has a language button)."""
    payload = {"v": 2}
    if item_type:
        payload["type"] = item_type
    payload["n"] = bi_value(name.replace("|", " "), texts.get("name_en", "").replace("|", " "))
    payload["l"] = items
    for key, short in (("hint", "h"), ("intro", "b"), ("footer", "f")):
        value = bi_value(texts.get(key, ""), texts.get(key + "_en", ""))
        if value:
            payload[short] = value
    if texts.get("vcard"):
        payload["vc"] = 1
    if texts.get("lang") in ("ar", "en"):
        payload["dl"] = texts["lang"]
    if logo_id:
        payload["lg"] = logo_id
    if logo_url:
        payload["lgu"] = logo_url
    if design_id:
        payload["d"] = design_id
    if design is not None:
        payload["dz"] = design
    return payload


def encode_payload(payload):
    text = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    compressor = zlib.compressobj(9, zlib.DEFLATED, -15)
    packed = compressor.compress(text.encode("utf-8")) + compressor.flush()
    return base64.urlsafe_b64encode(packed).decode("ascii").rstrip("=")


# =============================================================================
# PAGES STORED ON GITHUB (cards and menus, editable after engraving / NFC)
#   <pages repo>/items/<id>.json   the page itself (same data format as the link payload, v2)
#   <pages repo>/index.json        {"items": {id: {"t": type, "n": name, "u": time, "x": archived}}}
#   <assets repo>/img/<hash>.png   logos, backgrounds, dish photos
#   <templates repo>/templates/<slug>.json + index.json
# The id inside the QR code / NFC tag never changes, and an id is never deleted or reused:
# "deleting" a page only archives it (the page then says it is no longer available).
# =============================================================================
def new_item_id(existing):
    alphabet = string.ascii_lowercase + string.digits
    for _ in range(100):
        item_id = "".join(secrets.choice(alphabet) for _ in range(ITEM_ID_LEN))
        if item_id not in existing:
            return item_id
    raise ValueError("Could not create a free page id. Try again.")


def page_link(base, item_id):
    return base.split("#")[0].split("?")[0].rstrip("/") + "/?id=" + item_id


def _gh_headers(cfg):
    return {
        "Authorization": "Bearer " + cfg["token"],
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "QR-Studio",
    }


def github_get_file(cfg, path):
    """(bytes, sha) of <path> in cfg['repo'], or (None, None) when the file does not exist."""
    api = f"https://api.github.com/repos/{cfg['repo']}/contents/{path}"
    try:
        request = urllib.request.Request(api, headers=_gh_headers(cfg), method="GET")
        with urllib.request.urlopen(request, timeout=20, context=_ssl_context()) as response:
            data = json.loads(response.read().decode("utf-8"))
        return base64.b64decode(data.get("content", "")), data.get("sha")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None, None
        raise ValueError(_github_error_message(e.code, cfg["repo"], "the data").replace("uploading", "reading"))
    except Exception as e:
        print(f"[GitHub] read failed: {e}")
        raise ValueError("Could not reach GitHub. Check your internet connection.")


def _json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def upload_asset(cfg, name, data, what):
    """Uploads <img folder>/<name> to the assets repository (skipped when already there). Returns its public address."""
    path = f"{ASSET_IMG_FOLDER}/{name}"
    github_put_file(cfg, path, data, f"Add {what}", overwrite=False, what=what)
    return f"https://{cfg['owner']}.github.io/{cfg['repo'].split('/')[1]}/{path}"


def prepare_image(path, max_px, fmt="JPEG"):
    """Shrinks a picture. Returns (short id from the content, bytes, extension)."""
    img = Image.open(path)
    if fmt == "JPEG":
        img = img.convert("RGB")
        ext, options = "jpg", {"quality": 82, "optimize": True}
    else:
        img = img.convert("RGBA")
        ext, options = "png", {"optimize": True}
    img.thumbnail((max_px, max_px), RESAMPLE)
    buf = io.BytesIO()
    img.save(buf, format=fmt, **options)
    data = buf.getvalue()
    return hashlib.sha1(data).hexdigest()[:10], data, ext


def index_load(cfg):
    raw, _sha = github_get_file(cfg, INDEX_FILE)
    items = {}
    if raw:
        try:
            loaded = json.loads(raw.decode("utf-8")).get("items")
            if isinstance(loaded, dict):
                items = {k: v for k, v in loaded.items() if ITEM_ID_RE.match(k) and isinstance(v, dict)}
        except Exception:
            items = {}
    return {"items": items}


def index_save(cfg, index):
    github_put_file(cfg, INDEX_FILE, _json_bytes(index), "Update index", overwrite=True, what="the page list")


def publish_item(cfg, item_id, payload, display_name):
    """Writes items/<id>.json (new id when `item_id` is empty) and the index. Returns the id."""
    index = index_load(cfg)
    if not item_id:
        item_id = new_item_id(index["items"])
    github_put_file(
        cfg, f"{ITEMS_FOLDER}/{item_id}.json", _json_bytes(payload), f"Page {item_id}", overwrite=True, what="the page"
    )
    index["items"][item_id] = {"t": payload.get("type", "card"), "n": display_name[:60], "u": int(time.time()), "x": 0}
    index_save(cfg, index)
    return item_id


def fetch_item(cfg, item_id):
    raw, _sha = github_get_file(cfg, f"{ITEMS_FOLDER}/{item_id}.json")
    if raw is None:
        raise ValueError("That page was not found on GitHub.")
    obj = json.loads(raw.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("That page file is damaged.")
    return obj


def archive_item(cfg, item_id, archived):
    """Archive = the page shows 'no longer available'. The id stays reserved and can be restored."""
    obj = fetch_item(cfg, item_id)
    if archived:
        obj["x"] = 1
    else:
        obj.pop("x", None)
    github_put_file(
        cfg, f"{ITEMS_FOLDER}/{item_id}.json", _json_bytes(obj), f"Page {item_id}", overwrite=True, what="the page"
    )
    index = index_load(cfg)
    if item_id in index["items"]:
        index["items"][item_id]["x"] = 1 if archived else 0
        index_save(cfg, index)


def _main_text(value):
    ar, en = bi_parts(value)
    return ar or en


def texts_from_item(obj):
    """Stored page -> (Arabic/main name, texts dict) for the card editor."""
    texts = clean_texts(None)
    for key, short in (("hint", "h"), ("intro", "b"), ("footer", "f")):
        texts[key], texts[key + "_en"] = bi_parts(obj.get(short))
    name, texts["name_en"] = bi_parts(obj.get("n"))
    texts["vcard"] = 1 if obj.get("vc") else 0
    texts["lang"] = obj.get("dl") if obj.get("dl") in ("ar", "en") else ""
    return name, texts


def entries_from_item(obj):
    """Stored card -> editor entries (the inverse of compile_page)."""
    entries = []
    for item in (obj.get("l") if isinstance(obj.get("l"), list) else [])[:MAX_ENTRIES]:
        if not isinstance(item, dict):
            continue
        if item.get("i") == "_h":
            heading = new_heading()
            heading["title"] = _main_text(item.get("t"))[:80]
            entries.append(heading)
            continue
        name = ID_TO_NAME.get(item.get("i"))
        if not name:
            continue
        entry = new_entry(name)
        values = [v for v in item.get("v", []) if isinstance(v, str)][:MAX_VALUES] if isinstance(item.get("v"), list) else []
        entry["values"] = values or [""]
        labels = [_main_text(v) for v in item.get("lb", [])] if isinstance(item.get("lb"), list) else []
        entry["labels"] = (labels + [""] * len(values))[: len(entry["values"])]
        entry["title"] = _main_text(item.get("t"))[:80]
        entry["text"] = _main_text(item.get("s"))
        entry["group"] = 0 if item.get("gr") == 0 else 1
        entry["sv"] = str(item["sv"]) if item.get("sv") in (0, 1) else ""
        entries.append(entry)

    design = clean_design(obj.get("dz"))
    for index, entry in enumerate(entries):  # styles are stored by position
        style = design["e"].get(str(index))
        if style and entry["id"] != "_h":
            entry["style"] = {k: style.get(k, "") for k in ENTRY_STYLE_RULES}
        if design["ft"] == index and entry["id"] != "_h":
            entry["featured"] = 1
    return entries, design


# =============================================================================
# MENU (sections -> dishes / products), Arabic + English
# =============================================================================
MENU_MAX_SECTIONS = 40
MENU_MAX_ITEMS = 120


def new_menu_item():
    return {"name": "", "name_en": "", "desc": "", "desc_en": "", "price": "", "off": 0, "img": "", "img_url": ""}


def new_menu_section():
    return {"title": "", "title_en": "", "items": [new_menu_item()]}


def new_menu():
    return {
        "name": "", "name_en": "", "hint": "", "hint_en": "", "footer": "", "footer_en": "",
        "currency": "", "currency_en": "", "phone": "", "whatsapp": "", "lang": "",
        "logo_url": "", "sections": [new_menu_section()],
    }  # fmt: skip


def clean_menu(raw):
    out = new_menu()
    out["sections"] = []
    if not isinstance(raw, dict):
        out["sections"] = [new_menu_section()]
        return out
    for key in ("name", "name_en", "hint", "hint_en", "footer", "footer_en", "currency", "currency_en"):
        out[key] = _text(raw.get(key), 120)
    out["phone"] = _text(raw.get("phone"), 25)
    out["whatsapp"] = _text(raw.get("whatsapp"), 25)
    out["lang"] = raw.get("lang") if raw.get("lang") in ("ar", "en") else ""
    out["logo_url"] = raw.get("logo_url") if isinstance(raw.get("logo_url"), str) and IMG_RE.match(raw["logo_url"]) else ""
    for section in (raw.get("sections") if isinstance(raw.get("sections"), list) else [])[:MENU_MAX_SECTIONS]:
        if not isinstance(section, dict):
            continue
        clean = {"title": _text(section.get("title"), 80), "title_en": _text(section.get("title_en"), 80), "items": []}
        for item in (section.get("items") if isinstance(section.get("items"), list) else [])[:MENU_MAX_ITEMS]:
            if not isinstance(item, dict):
                continue
            entry = new_menu_item()
            for key in ("name", "name_en"):
                entry[key] = _text(item.get(key), 80)
            for key in ("desc", "desc_en"):
                entry[key] = _text(item.get(key))
            entry["price"] = _text(item.get("price"), 40)
            entry["off"] = 1 if item.get("off") else 0
            entry["img"] = _text(item.get("img"), 500)
            url = item.get("img_url")
            entry["img_url"] = url if isinstance(url, str) and IMG_RE.match(url) else ""
            clean["items"].append(entry)
        out["sections"].append(clean)
    if not out["sections"]:
        out["sections"] = [new_menu_section()]
    return out


def _clean_phone(value, label):
    value = (value or "").strip()
    if not value:
        return ""
    if not re.match(r"^\+?[0-9 ]{5,20}$", value):
        raise ValueError(f"{label}: use digits only, for example +213 555 12 34 56.")
    return value


def compile_menu(menu, design, logo_url=""):
    """Menu editor data -> the page payload (type 'menu'). Dishes without a name are dropped."""
    sections = []
    for section in menu["sections"]:
        items = []
        for it in section["items"]:
            name = bi_value(it["name"], it["name_en"])
            if not name:
                continue
            entry = {"t": name}
            desc = bi_value(it["desc"], it["desc_en"])
            if desc:
                entry["d"] = desc
            if it["price"].strip():
                entry["p"] = it["price"].strip()
            if it["off"]:
                entry["off"] = 1
            if it.get("img_url"):
                entry["img"] = it["img_url"]
            items.append(entry)
        if items:
            block = {"i": items}
            title = bi_value(section["title"], section["title_en"])
            if title:
                block["t"] = title
            sections.append(block)
    if not sections:
        raise ValueError("Add at least one dish or product with a name.")

    payload = {"v": 2, "type": "menu", "n": bi_value(menu["name"], menu["name_en"]), "s": sections}
    for key, short in (("hint", "h"), ("footer", "f")):
        value = bi_value(menu[key], menu[key + "_en"])
        if value:
            payload[short] = value
    currency = bi_value(menu["currency"], menu["currency_en"])
    if currency:
        payload["cur"] = currency
    phone = _clean_phone(menu["phone"], "Phone")
    whatsapp = _clean_phone(menu["whatsapp"], "WhatsApp")
    if phone:
        payload["ph"] = phone
    if whatsapp:
        payload["wa"] = whatsapp
    if menu.get("lang") in ("ar", "en"):
        payload["dl"] = menu["lang"]
    if logo_url:
        payload["lgu"] = logo_url
    final = clean_design(design)
    final["e"], final["ft"] = {}, -1
    payload["dz"] = final
    return payload


def menu_from_item(obj):
    """Stored menu -> editor data (the inverse of compile_menu)."""
    menu = new_menu()
    menu["name"], menu["name_en"] = bi_parts(obj.get("n"))
    menu["hint"], menu["hint_en"] = bi_parts(obj.get("h"))
    menu["footer"], menu["footer_en"] = bi_parts(obj.get("f"))
    menu["currency"], menu["currency_en"] = bi_parts(obj.get("cur"))
    menu["phone"] = _text(obj.get("ph"), 25)
    menu["whatsapp"] = _text(obj.get("wa"), 25)
    menu["lang"] = obj.get("dl") if obj.get("dl") in ("ar", "en") else ""
    menu["logo_url"] = obj.get("lgu") if isinstance(obj.get("lgu"), str) else ""
    menu["sections"] = []
    for block in (obj.get("s") if isinstance(obj.get("s"), list) else [])[:MENU_MAX_SECTIONS]:
        if not isinstance(block, dict):
            continue
        section = {"items": []}
        section["title"], section["title_en"] = bi_parts(block.get("t"))
        for it in (block.get("i") if isinstance(block.get("i"), list) else [])[:MENU_MAX_ITEMS]:
            if not isinstance(it, dict):
                continue
            item = new_menu_item()
            item["name"], item["name_en"] = bi_parts(it.get("t"))
            item["desc"], item["desc_en"] = bi_parts(it.get("d"))
            item["price"] = _text(it.get("p"), 40)
            item["off"] = 1 if it.get("off") else 0
            item["img_url"] = it.get("img") if isinstance(it.get("img"), str) else ""
            section["items"].append(item)
        menu["sections"].append(section)
    return clean_menu(menu), clean_design(obj.get("dz"))


# =============================================================================
# OFFLINE CODES (the data is inside the code, no internet needed)
# =============================================================================
OFFLINE_TYPES = ["Text", "Serial", "vCard", "WiFi", "Location", "Phone", "SMS", "Email", "Product"]
OFFLINE_MAX_BATCH = 5000
# (key, label, hint, kind)  kind: a = Arabic-capable text, l = plain, m = several lines
OFFLINE_FIELDS = {
    "Text": [("text", "Text", "Any text, number or code", "m")],
    "Serial": [
        ("prefix", "Prefix", "LOT25-", "l"),
        ("start", "First number", "1", "l"),
        ("count", "How many codes", "1", "l"),
        ("digits", "Digits (zero padded)", "4", "l"),
        ("suffix", "Suffix (optional)", "", "l"),
    ],
    "vCard": [
        ("name", "Full name", "Name", "a"),
        ("org", "Company", "Company", "a"),
        ("title", "Job title", "Job title", "a"),
        ("phone", "Phone", "+213 555 12 34 56", "l"),
        ("email", "Email", "name@example.com", "l"),
        ("url", "Website", "example.com", "l"),
        ("addr", "Address", "Address", "a"),
    ],
    "WiFi": [
        ("ssid", "Network name", "Network name (SSID)", "l"),
        ("password", "Password", "Password", "l"),
        ("sec", "Security: WPA, WEP or nopass", "WPA", "l"),
    ],
    "Location": [("lat", "Latitude", "36.7538", "l"), ("lng", "Longitude", "3.0588", "l")],
    "Phone": [("phone", "Phone number", "+213 555 12 34 56", "l")],
    "SMS": [("phone", "Phone number", "+213 555 12 34 56", "l"), ("message", "Message (optional)", "Message", "a")],
    "Email": [
        ("to", "To", "name@example.com", "l"),
        ("subject", "Subject (optional)", "Subject", "a"),
        ("body", "Message (optional)", "Message", "a"),
    ],
    "Product": [
        ("code", "Product code", "REF-001", "l"),
        ("name", "Name", "Product name", "a"),
        ("lot", "Lot / batch", "LOT25-01", "l"),
        ("date", "Date", "2026-11-17", "l"),
        ("size", "Size / weight", "40 x 60 cm", "l"),
        ("extra", "Extra note", "", "a"),
    ],
}
OFFLINE_NOTES = {
    "Text": "Any text. Scanners show it as text.",
    "Serial": "One code per number: prefix + number + suffix. Many codes at once are saved in one folder.",
    "vCard": "The phone offers to save a contact. Keep it short: every letter adds squares.",
    "WiFi": "The phone offers to join the network.",
    "Location": "Opens the map at these coordinates.",
    "Phone": "Opens the phone dialer.",
    "SMS": "Opens a text message.",
    "Email": "Opens the mail app.",
    "Product": "Readable lines (code, name, lot, date...). Any scanner can read them.",
}


def _wifi_escape(value):
    return re.sub(r'([\\;,:"])', r"\\\1", value)


def _vcard_escape(value):
    return value.replace("\\", "\\\\").replace("\n", "\\n").replace(";", "\\;").replace(",", "\\,")


def build_offline(kind, values):
    """Field values -> list of strings to encode (one string, or many for a serial batch). Raises ValueError."""

    def get(key):
        return (values.get(key) or "").strip()

    def need(key, label):
        if not get(key):
            raise ValueError(f"Fill in: {label}.")
        return get(key)

    if kind == "Text":
        return [need("text", "Text")]

    if kind == "Serial":
        try:
            start = int(get("start") or "1")
            count = int(get("count") or "1")
            digits = int(get("digits") or "1")
        except ValueError:
            raise ValueError("First number, count and digits must be whole numbers.")
        if start < 0 or digits < 1 or digits > 12:
            raise ValueError("First number must be 0 or more, digits between 1 and 12.")
        if not 1 <= count <= OFFLINE_MAX_BATCH:
            raise ValueError(f"How many codes: between 1 and {OFFLINE_MAX_BATCH}.")
        return [f"{get('prefix')}{n:0{digits}d}{get('suffix')}" for n in range(start, start + count)]

    if kind == "vCard":
        name = need("name", "Full name")
        lines = ["BEGIN:VCARD", "VERSION:3.0", f"FN:{_vcard_escape(name)}", f"N:{_vcard_escape(name)};;;;"]
        if get("org"):
            lines.append(f"ORG:{_vcard_escape(get('org'))}")
        if get("title"):
            lines.append(f"TITLE:{_vcard_escape(get('title'))}")
        if get("phone"):
            lines.append("TEL;TYPE=CELL:" + re.sub(r"[^\d+]", "", get("phone")))
        if get("email"):
            lines.append(f"EMAIL:{_vcard_escape(get('email'))}")
        if get("url"):
            lines.append(f"URL:{get('url')}")
        if get("addr"):
            lines.append(f"ADR:;;{_vcard_escape(get('addr'))};;;;")
        lines.append("END:VCARD")
        return ["\n".join(lines)]

    if kind == "WiFi":
        ssid = need("ssid", "Network name")
        security = (get("sec") or "WPA").upper()
        if security not in ("WPA", "WEP", "NOPASS"):
            raise ValueError("Security must be WPA, WEP or nopass.")
        if security == "NOPASS":
            return [f"WIFI:T:nopass;S:{_wifi_escape(ssid)};;"]
        return [f"WIFI:T:{security};S:{_wifi_escape(ssid)};P:{_wifi_escape(need('password', 'Password'))};;"]

    if kind == "Location":
        try:
            lat, lng = float(get("lat").replace(",", ".")), float(get("lng").replace(",", "."))
        except ValueError:
            raise ValueError("Latitude and longitude must be numbers.")
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            raise ValueError("Latitude is -90..90 and longitude -180..180.")
        return [f"geo:{lat:g},{lng:g}"]

    if kind == "Phone":
        return ["tel:" + re.sub(r"[^\d+]", "", need("phone", "Phone number"))]

    if kind == "SMS":
        number = re.sub(r"[^\d+]", "", need("phone", "Phone number"))
        return [f"SMSTO:{number}:{get('message')}"]

    if kind == "Email":
        to = need("to", "To")
        extras = []
        if get("subject"):
            extras.append("subject=" + quote(get("subject")))
        if get("body"):
            extras.append("body=" + quote(get("body")))
        return ["mailto:" + to + ("?" + "&".join(extras) if extras else "")]

    if kind == "Product":
        lines = []
        for key, label in (("code", "CODE"), ("name", "NAME"), ("lot", "LOT"), ("date", "DATE"), ("size", "SIZE"), ("extra", "NOTE")):
            if get(key):
                lines.append(f"{label}: {get(key)}")
        if not lines:
            raise ValueError("Fill in at least one product field.")
        return ["\n".join(lines)]

    raise ValueError("Unknown offline type.")


# =============================================================================
# ONLINE DESIGN TEMPLATES (templates repository: unlimited, no app update needed)
# =============================================================================
def template_slug(name):
    slug = re.sub(r"[^a-z0-9_-]+", "-", name.strip().lower()).strip("-")[:40]
    return slug or "template"


def templates_list(cfg):
    """{slug: display name} from the templates repository."""
    raw, _sha = github_get_file(cfg, INDEX_FILE)
    if not raw:
        return {}
    try:
        loaded = json.loads(raw.decode("utf-8")).get("templates")
        return {k: _text(v, 60) for k, v in loaded.items() if isinstance(k, str)} if isinstance(loaded, dict) else {}
    except Exception:
        return {}


def template_publish(cfg, name, design):
    slug = template_slug(name)
    github_put_file(
        cfg, f"templates/{slug}.json", design_json(design), f"Template {slug}", overwrite=True, what="the template"
    )
    listing = templates_list(cfg)
    listing[slug] = name.strip()[:60] or slug
    github_put_file(
        cfg, INDEX_FILE, _json_bytes({"templates": listing}), "Update template list", overwrite=True, what="the template list"
    )
    return slug


def template_fetch(cfg, slug):
    raw, _sha = github_get_file(cfg, f"templates/{slug}.json")
    if raw is None:
        raise ValueError("Template not found.")
    return clean_design(json.loads(raw.decode("utf-8")))



# --- projects (saved locally, inside the app data folder) -----------------------
def load_store(path):
    """{'projects': {...}, 'designs': {...}}; a missing or damaged file gives an empty store."""
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        projects = data.get("projects") if isinstance(data.get("projects"), dict) else {}
        designs = data.get("designs") if isinstance(data.get("designs"), dict) else {}
        return {"projects": projects, "designs": designs}
    except Exception:
        return {"projects": {}, "designs": {}}


def save_store(path, store):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(store, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def open_url(url):
    """Opens a web address in the browser (Android: through an intent)."""
    try:
        if IS_ANDROID:
            from jnius import autoclass

            intent_class = autoclass("android.content.Intent")
            uri_class = autoclass("android.net.Uri")
            activity = autoclass("org.kivy.android.PythonActivity").mActivity
            activity.startActivity(intent_class(intent_class.ACTION_VIEW, uri_class.parse(url)))
            return True
        import webbrowser

        return bool(webbrowser.open(url))
    except Exception as e:
        print(f"[Browser] {e}")
        return False


# =============================================================================
# QR GENERATION
# =============================================================================
def logo_path(key, number="1"):
    return os.path.join(LOGO_FOLDER, PLATFORM_PREFIX[key] + number + ".png")


def logo_number(style):
    return "1" if style == "Color" else "2"


def load_logo(key, style):
    path = logo_path(key, logo_number(style))
    if os.path.isfile(path):
        return Image.open(path).convert("RGBA")
    return None


def _fit_qr(content, with_logo, **options):
    """Smallest QR for `content`: level L without logo, level M with logo (the logo hides modules)."""
    level = qrcode.constants.ERROR_CORRECT_M if with_logo else qrcode.constants.ERROR_CORRECT_L
    qr = qrcode.QRCode(version=None, error_correction=level, **options)
    qr.add_data(content)
    qr.make(fit=True)
    return qr


def qr_version(content, with_logo=False):
    return _fit_qr(content, with_logo, border=0).version


def make_qr(content, with_logo, max_version=MAX_VERSION):
    """Smallest QR for `content`. Refuses anything above `max_version` so a dense code
    never reaches the laser by accident."""
    qr = _fit_qr(content, with_logo, box_size=BOX_SIZE, border=BORDER_MODULES)
    if qr.version > max_version:
        side = 17 + 4 * qr.version
        limit = 17 + 4 * max_version
        if max_version > MAX_VERSION:
            raise ValueError(
                f"Too much data: the code would be {side}x{side} squares (limit {limit}x{limit}). "
                f"Shorten the content."
            )
        raise ValueError(
            f"Link too long for engraving: the code would be {side}x{side} squares. "
            f"Try the 'Short' link type or a shorter link."
        )
    return qr


def pick_single(link, link_type, with_logo):
    """Returns (content, route). Direct links open the app straight from the scanner."""
    if link.lower().startswith(CONTACT_SCHEMES):
        return link, "contact"  # never shortened: a web shortener cannot open mail/phone apps
    if link_type == "Direct":
        return link, "direct"
    version = qr_version(link, with_logo)
    if link_type == "Auto" and version <= AUTO_DIRECT_MAX_VERSION:
        return link, "direct"
    try:
        return shorten_url(link), "short"
    except ValueError:
        if link_type == "Auto" and version <= MAX_VERSION:
            return link, "fallback"
        raise


def _logo_window(badge, matrix_size, data_modules):
    """Shrinks `badge` to fit and returns (first module, modules covered) of the square
    cleared in the middle of the code. The size is kept odd so the window stays centered."""
    logo_px = int(data_modules * BOX_SIZE * CENTER_LOGO_RATIO)
    badge.thumbnail((logo_px, logo_px), RESAMPLE)
    cap = max(3, int(data_modules * CENTER_LOGO_MAX_RATIO))
    reserve = min(math.ceil(badge.width / BOX_SIZE) + 1, cap)
    if reserve % 2 == 0:
        reserve += 1 if reserve < cap else -1
    return (matrix_size - reserve) // 2, reserve


def generate_qr(content, key, logo_style, show_logo, max_version=MAX_VERSION):
    """PNG for print. Black on white, quiet zone included. Returns the PIL image."""
    badge = load_logo(key, logo_style) if (key != ALL_KEY and show_logo) else None
    qr = make_qr(content, with_logo=badge is not None, max_version=max_version)

    matrix = qr.get_matrix()
    n = len(matrix)
    size = n * BOX_SIZE

    image = Image.new("RGBA", (size, size), "#FFFFFF")
    draw = ImageDraw.Draw(image)

    start, reserve = 0, 0
    if badge:
        start, reserve = _logo_window(badge, n, n - 2 * BORDER_MODULES)
    end = start + reserve  # empty window when there is no logo

    for r in range(n):
        for c in range(n):
            if not matrix[r][c]:
                continue
            if badge and start <= r < end and start <= c < end:
                continue
            x, y = c * BOX_SIZE, r * BOX_SIZE
            draw.rectangle((x, y, x + BOX_SIZE - 1, y + BOX_SIZE - 1), fill="#000000")

    if badge:
        bx = by = start * BOX_SIZE
        window = reserve * BOX_SIZE
        draw.rectangle((bx, by, bx + window - 1, by + window - 1), fill="#FFFFFF")
        image.alpha_composite(badge, (bx + (window - badge.width) // 2, by + (window - badge.height) // 2))

    return image


def _svg_path(matrix):
    """Horizontal runs of dark modules as one SVG path (1 unit = 1 module)."""
    size = len(matrix)
    parts = []
    for r, row in enumerate(matrix):
        c = 0
        while c < size:
            if not row[c]:
                c += 1
                continue
            start = c
            while c < size and row[c]:
                c += 1
            parts.append(f"M{start} {r}h{c - start}v1h-{c - start}z")
    return "".join(parts)


def save_svg(content, path, size_mm, max_version=MAX_VERSION):
    """Vector file for laser/CNC/CorelDRAW. Black squares only, no logo, no background.
    The drawing is cropped to the code itself: its width is exactly `size_mm`.
    Returns (modules per side, millimetres per square)."""
    full = make_qr(content, with_logo=False, max_version=max_version).get_matrix()
    b = BORDER_MODULES
    matrix = [row[b : len(row) - b] for row in full[b : len(full) - b]]
    modules = len(matrix)

    svg = (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{size_mm}mm" height="{size_mm}mm" '
        f'viewBox="0 0 {modules} {modules}" shape-rendering="crispEdges">'
        f'<path d="{_svg_path(matrix)}" fill="#000000"/></svg>'
    )
    with open(path, "w", encoding="utf-8") as f:
        f.write(svg)
    return modules, size_mm / modules


# =============================================================================
# UI PRIMITIVES
# =============================================================================
def paint(widget, color, radius=None):
    """Rounded background behind a widget."""
    radius = dp(10) if radius is None else radius
    with widget.canvas.before:
        Color(*color)
        rect = RoundedRectangle(radius=[radius])

    def update(*_):
        rect.pos = widget.pos
        rect.size = widget.size

    widget.bind(pos=update, size=update)
    update()
    return rect


def _fit_text(label):
    """Makes a label wrap and align inside its own box."""
    label.bind(size=lambda w, s: setattr(w, "text_size", (s[0], s[1])))
    return label


def make_label(text, size="13sp", color=MUTED, bold=False, height=None, arabic=False):
    """arabic=True: the text is shaped for Arabic and drawn with an Arabic font (set it again with shape())."""
    height = dp(24) if height is None else height
    extra = {"font_name": AR_FONT} if (arabic and AR_FONT) else {}
    label = Label(
        text=shape(text) if arabic else text,
        **extra,
        font_size=size,
        color=color,
        bold=bold,
        size_hint_y=None,
        height=height,
        halign="left",
        valign="middle",
    )
    return _fit_text(label)


def make_section(text):
    return make_label(text.upper(), size="11sp", color=MUTED, bold=True, height=dp(20))


def make_note(text, height=None):
    height = dp(34) if height is None else height
    label = Label(
        text=text, font_size="11sp", color=MUTED, size_hint_y=None, height=height, halign="left", valign="top"
    )
    return _fit_text(label)


class ContextMenuInput(TextInput):
    """Right-click menu on desktop. Phones use the native long-press menu."""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.menu = DropDown()
        actions = [("Cut", self._cut), ("Copy", self._copy), ("Paste", self._paste), ("Select All", self._select_all)]
        for label, callback in actions:
            button = Button(text=label, size_hint_y=None, height=dp(34), background_color=(0.2, 0.2, 0.28, 1))
            button.bind(on_release=lambda _btn, cb=callback: cb())
            self.menu.add_widget(button)

    def on_touch_down(self, touch):
        if getattr(touch, "button", None) == "right" and self.collide_point(*touch.pos):
            self.focus = True
            self.menu.open(self)
            return True
        return super().on_touch_down(touch)

    def _cut(self):
        if self.selection_text:
            Clipboard.copy(self.selection_text)
            self.delete_selection()
        self.menu.dismiss()

    def _copy(self):
        if self.selection_text:
            Clipboard.copy(self.selection_text)
        self.menu.dismiss()

    def _paste(self):
        content = Clipboard.paste()
        if content:
            self.insert_text(content)
        self.menu.dismiss()

    def _select_all(self):
        self.select_all()
        self.menu.dismiss()


class ArabicInput(ContextMenuInput):
    """Text field that shows Arabic correctly (joined letters, right-to-left).

    Kivy cannot shape Arabic by itself, so the real text lives in `logical` (this is what the app saves and
    uploads) and the field only DISPLAYS the shaped version. While the text has no Arabic letter the field
    behaves like a normal one. Once it has Arabic, typing adds to the end and Backspace removes the last
    letter; select-all + delete/cut clears the field. Latin-only fields are never affected.
    """

    logical = StringProperty("")

    def __init__(self, **kwargs):
        initial = kwargs.pop("text", "")
        if AR_FONT:
            kwargs.setdefault("font_name", AR_FONT)
        super().__init__(**kwargs)
        self.set_logical(initial)

    # ---- value ----
    def set_logical(self, value):
        self.logical = value or ""
        self._refresh()

    def _refresh(self):
        shown = shape(self.logical)
        if shown != self.text:
            self.text = shown
        Clock.schedule_once(self._cursor_to_end, 0)

    def _cursor_to_end(self, *_):
        try:
            self.cursor = self.get_cursor_from_index(len(self.text))
        except Exception:
            pass

    def _drop_selection(self):
        if self.selection_text:
            if len(self.selection_text) >= len(self.text):
                self.logical = ""
            self.cancel_selection()

    # ---- editing ----
    def insert_text(self, substring, from_undo=False):
        if not has_arabic(self.logical) and not has_arabic(substring):
            super().insert_text(substring, from_undo=from_undo)
            self.logical = self.text
            return
        self._drop_selection()
        self.logical += substring
        self._refresh()

    def do_backspace(self, from_undo=False, mode="bkspc"):
        if not has_arabic(self.logical):
            super().do_backspace(from_undo=from_undo, mode=mode)
            self.logical = self.text
            return
        if self.selection_text and len(self.selection_text) >= len(self.text):
            self.logical = ""
            self.cancel_selection()
        elif mode == "del":
            return
        else:
            self.logical = self.logical[:-1]
        self._refresh()

    def delete_selection(self, from_undo=False):
        if not has_arabic(self.logical):
            super().delete_selection(from_undo=from_undo)
            self.logical = self.text
            return
        self._drop_selection()
        self._refresh()

    # ---- clipboard: always the real text, never the shaped one ----
    def copy(self, data=""):
        if has_arabic(self.logical) and not data:
            Clipboard.copy(self.logical)
        else:
            super().copy(data)

    def _copy(self):
        self.copy()
        self.menu.dismiss()

    def _cut(self):
        if has_arabic(self.logical):
            Clipboard.copy(self.logical)
            self.set_logical("")
            self.menu.dismiss()
        else:
            super()._cut()
            self.logical = self.text


class FieldBox(BoxLayout):
    """Rounded text field. Use `.text` like a normal input.
    arabic=True: the field shows Arabic correctly; `.text` is then the real (logical) text.
    Listen to changes with bind_value(callback)."""

    def __init__(self, hint="", height=None, text="", arabic=False, **kw):
        height = dp(46) if height is None else height
        kw.setdefault("size_hint_y", None)
        super().__init__(height=height, padding=[dp(12), 0, dp(12), 0], **kw)
        self.arabic = arabic
        with self.canvas.before:
            self._bcol = Color(*BORDER)
            self._brect = RoundedRectangle(radius=[dp(10)])
            Color(*FIELD)
            self._frect = RoundedRectangle(radius=[dp(9)])
        self.bind(pos=self._upd, size=self._upd)

        self.input = (ArabicInput if arabic else ContextMenuInput)(
            hint_text=hint,
            text=text,
            multiline=False,
            font_size="15sp",
            padding=[0, (height - dp(20)) / 2, 0, 0],
            background_normal="",
            background_active="",
            background_color=(0, 0, 0, 0),
            foreground_color=TEXT,
            hint_text_color=MUTED,
            cursor_color=ACCENT,
            selection_color=rgba("#4F8CFF", 0.35),
        )
        self.input.bind(focus=self._on_focus)
        self.add_widget(self.input)
        self._upd()

    def _upd(self, *_):
        self._brect.pos = self.pos
        self._brect.size = self.size
        self._frect.pos = (self.x + dp(1), self.y + dp(1))
        self._frect.size = (self.width - dp(2), self.height - dp(2))

    def _on_focus(self, _input, focused):
        self._bcol.rgba = ACCENT if focused else BORDER

    @property
    def text(self):
        return self.input.logical if self.arabic else self.input.text

    @text.setter
    def text(self, value):
        if self.arabic:
            self.input.set_logical(value)
        else:
            self.input.text = value

    def bind_value(self, callback):
        """callback(value) on every change of the real text."""
        if self.arabic:
            self.input.bind(logical=lambda _i, v: callback(v))
        else:
            self.input.bind(text=lambda _i, v: callback(v))


class RoundedButton(Button):
    """Flat rounded button that brightens while pressed."""

    def __init__(self, bg=ACCENT, fg=TEXT, radius=None, **kw):
        radius = dp(10) if radius is None else radius
        kw.setdefault("font_size", "15sp")
        kw.setdefault("bold", True)
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(48))
        super().__init__(background_normal="", background_down="", background_color=(0, 0, 0, 0), color=fg, **kw)
        self._bg = bg
        with self.canvas.before:
            self._col = Color(*bg)
            self._rect = RoundedRectangle(radius=[radius])
        self.bind(pos=self._upd, size=self._upd)
        self.bind(on_press=lambda *_: self._shade(True), on_release=lambda *_: self._shade(False))
        self.bind(disabled=lambda w, v: setattr(w, "opacity", 0.45 if v else 1))
        self._upd()

    def _upd(self, *_):
        self._rect.pos = self.pos
        self._rect.size = self.size

    def _shade(self, pressed):
        c = self._bg
        self._col.rgba = (min(1, c[0] * 1.2), min(1, c[1] * 1.2), min(1, c[2] * 1.2), c[3]) if pressed else c

    def set_bg(self, bg):
        self._bg = bg
        self._col.rgba = bg


class Segmented(BoxLayout):
    """Pill-style option picker."""

    def __init__(self, options, selected, on_select=None, **kw):
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(42))
        kw.setdefault("spacing", dp(6))
        super().__init__(**kw)
        self.options = options
        self.value = selected
        self.on_select = on_select
        self.buttons = {}
        for option in options:
            button = RoundedButton(text=option, bg=SURFACE2, fg=MUTED, radius=dp(9), height=dp(42), font_size="13sp")
            button.bind(on_release=lambda _btn, o=option: self.select(o))
            self.buttons[option] = button
            self.add_widget(button)
        self._paint()

    def select(self, value, notify=True):
        self.value = value
        self._paint()
        if notify and self.on_select:
            self.on_select(value)

    def _paint(self):
        for option, button in self.buttons.items():
            selected = option == self.value
            button.set_bg(ACCENT if selected else SURFACE2)
            button.color = TEXT if selected else MUTED


class Card(BoxLayout):
    """Titled panel that grows with its content."""

    def __init__(self, title=None, **kw):
        kw.setdefault("orientation", "vertical")
        kw.setdefault("padding", dp(16))
        kw.setdefault("spacing", dp(10))
        kw.setdefault("size_hint_y", None)
        super().__init__(**kw)
        with self.canvas.before:
            Color(*BORDER)
            self._border = RoundedRectangle(radius=[dp(14)])
            Color(*SURFACE)
            self._bg = RoundedRectangle(radius=[dp(13)])
        self.bind(pos=self._upd, size=self._upd, minimum_height=self.setter("height"))
        if title:
            self.add_widget(make_section(title))

    def _upd(self, *_):
        self._border.pos = self.pos
        self._border.size = self.size
        self._bg.pos = (self.x + dp(1), self.y + dp(1))
        self._bg.size = (self.width - dp(2), self.height - dp(2))


class Stat(BoxLayout):
    """Small value + caption tile."""

    def __init__(self, caption, **kw):
        super().__init__(
            orientation="vertical",
            size_hint_y=None,
            height=dp(56),
            spacing=dp(2),
            padding=[dp(4), dp(8), dp(4), dp(6)],
            **kw,
        )
        paint(self, SURFACE2, dp(10))
        self.value = make_label("-", size="16sp", bold=True, color=TEXT, height=dp(22))
        self.value.halign = "center"
        caption_label = make_label(caption, size="10sp", height=dp(14))
        caption_label.halign = "center"
        self.add_widget(self.value)
        self.add_widget(caption_label)

    def set(self, text):
        self.value.text = text


class LogoTile(ButtonBehavior, BoxLayout):
    """Selectable platform tile (logo + name)."""

    def __init__(self, name, key, **kw):
        super().__init__(orientation="vertical", padding=dp(6), spacing=dp(2), **kw)
        self.key = key
        with self.canvas.before:
            self._bcol = Color(*BORDER)
            self._brect = RoundedRectangle(radius=[dp(10)])
            self._fcol = Color(*SURFACE2)
            self._frect = RoundedRectangle(radius=[dp(9)])
        self.bind(pos=self._upd, size=self._upd)

        path = logo_path(key)
        if os.path.isfile(path):
            self.add_widget(KivyImage(source=path, fit_mode="contain"))
        else:
            self.add_widget(Label(text=name[:1], font_size="20sp", bold=True, color=TEXT))
        self._name = Label(text=name, font_size="10sp", color=MUTED, size_hint_y=None, height=dp(16))
        self.add_widget(self._name)
        self._upd()

    def _upd(self, *_):
        self._brect.pos = self.pos
        self._brect.size = self.size
        self._frect.pos = (self.x + dp(1.5), self.y + dp(1.5))
        self._frect.size = (self.width - dp(3), self.height - dp(3))

    def set_selected(self, selected):
        self._bcol.rgba = ACCENT if selected else BORDER
        self._fcol.rgba = ACCENT_SOFT if selected else SURFACE2
        self._name.color = TEXT if selected else MUTED


# =============================================================================
# DESIGN EDITOR WIDGETS
# =============================================================================
PALETTE = [
    "#ffffff", "#e5e7eb", "#9ca3af", "#4b5563", "#111827", "#000000",
    "#ef4444", "#f97316", "#f59e0b", "#eab308", "#84cc16", "#22c55e",
    "#10b981", "#14b8a6", "#06b6d4", "#0ea5e9", "#3b82f6", "#6366f1",
    "#8b5cf6", "#a855f7", "#d946ef", "#ec4899", "#f43f5e", "#0a0f1e",
]  # fmt: skip


def _snap(value, step):
    """Rounds a slider value to its step (int for whole steps)."""
    if isinstance(step, int):
        return int(round(value / step) * step)
    return round(round(value / step) * step, 4)


def _popup(title, size_hint=(0.96, 0.92)):
    popup = Popup(title=title, size_hint=size_hint)
    popup.title_color = TEXT
    popup.background = ""
    popup.background_color = SURFACE
    popup.separator_color = ACCENT
    return popup


class Swatch(ButtonBehavior, Widget):
    """Small coloured square; tapping it opens the palette."""

    def __init__(self, color, **kw):
        super().__init__(size_hint=(None, 1), width=dp(42), **kw)
        with self.canvas.before:
            Color(*BORDER)
            self._border = RoundedRectangle(radius=[dp(10)])
            self._col = Color(*color)
            self._rect = RoundedRectangle(radius=[dp(9)])
        self.bind(pos=self._upd, size=self._upd)
        self._upd()

    def _upd(self, *_):
        self._border.pos, self._border.size = self.pos, self.size
        self._rect.pos = (self.x + dp(1.5), self.y + dp(1.5))
        self._rect.size = (self.width - dp(3), self.height - dp(3))

    def set_color(self, color):
        self._col.rgba = color


class ColorField(BoxLayout):
    """Hex colour input + swatch with a palette. `allow_empty` means 'use the default'."""

    def __init__(self, value, on_change, allow_empty=False, **kw):
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(42))
        kw.setdefault("spacing", dp(8))
        super().__init__(**kw)
        self.on_change = on_change
        self.allow_empty = allow_empty
        self.swatch = Swatch(rgba(value) if HEX_RE.match(value or "") else (0, 0, 0, 0))
        self.swatch.bind(on_release=self._open_palette)
        self.field = FieldBox("#RRGGBB" + (" or empty" if allow_empty else ""), height=dp(42), text=value or "")
        self.field.input.bind(text=self._changed)
        self.add_widget(self.swatch)
        self.add_widget(self.field)

    def _changed(self, _input, text):
        text = text.strip()
        if HEX_RE.match(text):
            self.swatch.set_color(rgba(text))
            self.on_change(text.lower())
        elif text == "" and self.allow_empty:
            self.swatch.set_color((0, 0, 0, 0))
            self.on_change("")

    def _open_palette(self, *_):
        popup = _popup("Pick a colour", (0.9, None))
        grid = GridLayout(cols=6, spacing=dp(8), padding=dp(10), size_hint_y=None, row_default_height=dp(44))
        grid.bind(minimum_height=grid.setter("height"))

        def pick(color):
            self.field.text = color
            popup.dismiss()

        for color in PALETTE:
            button = RoundedButton(text="", bg=rgba(color), radius=dp(8), height=dp(44))
            button.bind(on_release=lambda _b, c=color: pick(c))
            grid.add_widget(button)
        box = BoxLayout(orientation="vertical", spacing=dp(8))
        box.add_widget(grid)
        box.add_widget(RoundedButton(text="Close", bg=SURFACE2, on_release=popup.dismiss))
        popup.content = box
        popup.height = dp(260)
        popup.open()


def make_control(target, key, spec, on_change=None):
    """One labelled control that writes into target[key].
    spec = (key, label, kind, extra); kinds: color, color0, num (min, max, step), enum [(value, label)], bool, font,
    text / area (extra = hint)."""
    _key, label, kind, extra = spec
    box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(4))

    def put(value):
        target[key] = value
        if on_change:
            on_change()

    caption = make_label(label, size="12sp", height=dp(18))
    box.add_widget(caption)

    if kind in ("color", "color0"):
        box.add_widget(ColorField(target.get(key, ""), put, allow_empty=(kind == "color0")))
        box.height = dp(18) + dp(42) + dp(4)
    elif kind == "num":
        low, high, step = extra
        caption.text = f"{label}: {target.get(key, low)}"
        slider = Slider(min=low, max=high, step=step, value=target.get(key, low), size_hint_y=None, height=dp(36))

        def moved(_slider, value):
            value = _snap(value, step)
            if value != target.get(key):
                caption.text = f"{label}: {value}"
                put(value)

        slider.bind(value=moved)
        box.add_widget(slider)
        box.height = dp(18) + dp(36) + dp(4)
    elif kind in ("text", "area"):
        tall = kind == "area"
        field = FieldBox(extra or "", height=dp(150) if tall else dp(42), text=target.get(key, ""))
        if tall:
            field.input.multiline = True
            field.input.padding = [0, dp(12), 0, 0]
        field.bind_value(put)
        box.add_widget(field)
        box.height = dp(18) + field.height + dp(4)
    elif kind == "font":
        button = RoundedButton(text=target.get(key, FONT_CHOICES[0]), bg=SURFACE2, height=dp(42), font_size="13sp")

        def cycle(*_):
            current = FONT_CHOICES.index(target[key]) if target.get(key) in FONT_CHOICES else -1
            target[key] = FONT_CHOICES[(current + 1) % len(FONT_CHOICES)]
            button.text = target[key]
            put(target[key])

        button.bind(on_release=cycle)
        box.add_widget(button)
        box.height = dp(18) + dp(42) + dp(4)
    else:
        options = [(1, "On"), (0, "Off")] if kind == "bool" else extra
        labels = {value: text for value, text in options}
        by_label = {text: value for value, text in options}
        current = labels.get(target.get(key), options[0][1])
        seg = Segmented(
            [text for _v, text in options], current, on_select=lambda text: put(by_label[text]), height=dp(42)
        )
        box.add_widget(seg)
        box.height = dp(18) + dp(42) + dp(4)
    return box


# (group, tab title, [(key, label, kind, extra)])
DESIGN_TABS = [
    ("bg", "Page", [
        ("m", "Background", "enum", [("solid", "Solid"), ("gradient", "Gradient")]),
        ("c1", "Colour 1", "color", None),
        ("c2", "Gradient colour 2", "color", None),
        ("c3", "Gradient colour 3 (optional)", "color0", None),
        ("a", "Gradient angle", "num", (0, 360, 5)),
        ("gl", "Animated glow", "bool", None),
        ("g1", "Glow colour 1", "color", None),
        ("g2", "Glow colour 2", "color", None),
        ("g3", "Glow colour 3", "color", None),
        (
            "pt",
            "Pattern",
            "enum",
            [("none", "None"), ("dots", "Dots"), ("lines", "Lines"), ("grid", "Grid"), ("waves", "Waves")],
        ),
        ("pc", "Pattern colour", "color", None),
        ("po", "Pattern strength", "num", (0, 0.5, 0.01)),
        ("bi", "Background picture address (or use 'Background file' below)", "text", "https://....github.io/a/img/..."),
        ("bl", "Picture blur (the text is never blurred)", "num", (0, 40, 1)),
        ("dm", "Picture dimming", "num", (0, 0.9, 0.05)),
    ]),
    ("tx", "Text", [
        ("f", "Font (tap to change)", "font", None),
        ("ff", "Any Google Fonts name (overrides the font above)", "text", "e.g. Tajawal, Rubik, Lalezar"),
        ("c", "Text colour", "color", None),
        ("mu", "Secondary text colour", "color", None),
        ("tg", "Name uses a gradient", "bool", None),
        ("n1", "Name colour 1", "color", None),
        ("n2", "Name colour 2", "color", None),
        ("n3", "Name colour 3", "color", None),
        ("s", "Name size", "num", (18, 52, 1)),
        ("al", "Header alignment", "enum", [("c", "Centre"), ("s", "Start"), ("e", "End")]),
    ]),
    ("av", "Avatar", [
        ("sh", "Shape", "enum", [("c", "Circle"), ("r", "Rounded"), ("s", "Square")]),
        ("sz", "Size", "num", (70, 160, 2)),
        ("rg", "Ring", "enum", [("g", "Gradient"), ("s", "Solid"), ("n", "None")]),
        ("rc", "Solid ring colour", "color", None),
        ("ab", "Inner colour", "color", None),
        ("gw", "Glow", "bool", None),
    ]),
    ("cd", "Cards", [
        ("st", "Style", "enum", [("glass", "Glass"), ("solid", "Solid"), ("outline", "Outline"), ("flat", "Flat")]),
        ("r", "Corner radius", "num", (0, 36, 1)),
        ("cb", "Card colour (empty = automatic)", "color0", None),
        ("bd", "Border colour (empty = automatic)", "color0", None),
        ("sh", "Shadow on hover", "bool", None),
        ("gap", "Space between cards", "num", (4, 28, 1)),
        ("pd", "Card padding", "num", (6, 24, 1)),
        ("tl", "Icon style", "enum", [("white", "White"), ("soft", "Soft"), ("none", "None"), ("round", "Round")]),
        ("ts", "Icon size", "num", (36, 76, 2)),
        ("br", "Brand colours", "bool", None),
        ("ac", "One accent colour (brand colours off)", "color", None),
        ("sv", "Show addresses and numbers", "bool", None),
    ]),
    ("ly", "Layout", [
        ("m", "Layout", "enum", [("list", "List"), ("grid", "Grid"), ("icons", "Icons")]),
        ("ex", "Open groups", "enum", [("one", "One at a time"), ("many", "Several")]),
        ("cnt", "Show links counter", "bool", None),
        ("lang", "Show language button", "bool", None),
        ("hint", "Show hint line", "bool", None),
    ]),
    ("x", "More", [
        ("css", "Custom CSS for this page (empty = none). Anything with url(), @import or scripts is ignored.", "area",
         ".name { letter-spacing: 2px; }"),
    ]),
]  # fmt: skip

ENTRY_STYLE_SPECS = [
    ("ac", "Accent colour (empty = automatic)", "color0", None),
    ("cb", "Card colour (empty = design)", "color0", None),
    (
        "tl",
        "Icon style",
        "enum",
        [("", "Design"), ("white", "White"), ("soft", "Soft"), ("none", "None"), ("round", "Round")],
    ),
    ("sz", "Card size", "enum", [("", "Auto"), ("f", "Full"), ("h", "Half")]),
]


class DesignPopup(Popup):
    """Page appearance: templates + one tab per area."""

    def __init__(self, app, **kw):
        super().__init__(**kw)
        self.app = app
        self.title = "Page design"
        self.title_color = TEXT
        self.background = ""
        self.background_color = SURFACE
        self.separator_color = ACCENT
        self.size_hint = (0.97, 0.94)
        self.tab = DESIGN_TABS[0][0]

        layout = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        layout.add_widget(make_section("Templates"))
        self.templates_row = BoxLayout(size_hint_x=None, spacing=dp(6), height=dp(40))
        self.templates_row.bind(minimum_width=self.templates_row.setter("width"))
        strip = ScrollView(size_hint_y=None, height=dp(44), do_scroll_y=False, bar_width=0)
        strip.add_widget(self.templates_row)
        layout.add_widget(strip)
        self._fill_templates()

        self.tabs = Segmented([t[1] for t in DESIGN_TABS], DESIGN_TABS[0][1], on_select=self._on_tab, height=dp(40))
        layout.add_widget(self.tabs)

        self.grid = GridLayout(cols=1, spacing=dp(10), padding=[0, dp(4), dp(4), dp(4)], size_hint_y=None)
        self.grid.bind(minimum_height=self.grid.setter("height"))
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(self.grid)
        layout.add_widget(scroll)

        layout.add_widget(make_section("Public design name (optional, lets you restyle the page later)"))
        self.name_field = FieldBox("e.g. boujlida", text=app.design_name, height=dp(42))
        self.name_field.input.bind(text=lambda _i, v: setattr(app, "design_name", v))
        layout.add_widget(self.name_field)

        row = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(6))
        for text, callback in (
            ("Preview", lambda *_: app.preview_in_browser()),
            ("Save template", self._save_template),
            ("Update online", lambda *_: app.update_design_online()),
            ("Close", self.dismiss),
        ):
            row.add_widget(
                RoundedButton(
                    text=text,
                    bg=ACCENT if text == "Preview" else SURFACE2,
                    height=dp(44),
                    font_size="12sp",
                    on_release=callback,
                )
            )
        layout.add_widget(row)

        row2 = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(6))
        for text, callback in (
            ("Background file", self._pick_background),
            ("Online templates", lambda *_: OnlineTemplatesPopup(app, self).open()),
            ("Publish template", self._publish_template),
        ):
            row2.add_widget(RoundedButton(text=text, bg=SURFACE2, height=dp(44), font_size="12sp", on_release=callback))
        layout.add_widget(row2)
        self.content = layout
        self._show_tab()

    def _pick_background(self, *_):
        self.app.pick_file("Choose a background picture", ["*.png", "*.jpg", "*.jpeg", "*.webp"], self.app.set_background_file)

    def _publish_template(self, *_):
        name = self.name_field.text.strip()
        if not name:
            self.app.set_status("Type a design name first (field above the buttons).", ERROR)
            return
        cfgs = self.app.require_github()
        if not cfgs:
            return
        design = clean_design(self.app.design)
        self.app.set_status("Publishing the template...", MUTED)

        def done(slug, error):
            self.app.set_status(error or f"Template published: {name}", ERROR if error else SUCCESS)

        self.app.run_bg(lambda: template_publish(cfgs[2], name, design), done)

    def _fill_templates(self):
        self.templates_row.clear_widgets()
        names = list(TEMPLATES) + ["* " + n for n in self.app.store["designs"]]
        for name in names:
            button = RoundedButton(
                text=name, bg=SURFACE2, height=dp(40), size_hint_x=None, width=dp(24 + 9 * len(name)), font_size="12sp"
            )
            button.bind(on_release=lambda _b, n=name: self._apply_template(n))
            self.templates_row.add_widget(button)

    def _apply_template(self, name):
        if name.startswith("* "):
            self.app.design = clean_design(self.app.store["designs"].get(name[2:]))
        else:
            self.app.design = template_design(name)
        self._show_tab()
        self.app.set_status(f"Template applied: {name.lstrip('* ')}", SUCCESS)

    def _save_template(self, *_):
        name = self.name_field.text.strip() or "My design"
        self.app.store["designs"][name] = clean_design(self.app.design)
        self.app.save_store()
        self._fill_templates()
        self.app.set_status(f"Design saved as template: {name}", SUCCESS)

    def _on_tab(self, title):
        for group, tab_title, _specs in DESIGN_TABS:
            if tab_title == title:
                self.tab = group
        self._show_tab()

    def _show_tab(self):
        self.grid.clear_widgets()
        for group, _title, specs in DESIGN_TABS:
            if group == self.tab:
                for spec in specs:
                    self.grid.add_widget(make_control(self.app.design[group], spec[0], spec))


class EntryStylePopup(Popup):
    """Extra options of one link card."""

    def __init__(self, app, index, **kw):
        super().__init__(**kw)
        entry = app.entries[index]
        self.title = f"Card options: {entry['title'] or entry['name']}"
        self.title_color = TEXT
        self.background = ""
        self.background_color = SURFACE
        self.separator_color = ACCENT
        self.size_hint = (0.96, 0.9)

        grid = GridLayout(cols=1, spacing=dp(10), padding=[0, dp(4), dp(4), dp(4)], size_hint_y=None)
        grid.bind(minimum_height=grid.setter("height"))

        grid.add_widget(make_label("TEXT UNDER THE NAME (empty = hidden)", size="11sp", bold=True, height=dp(20)))
        text_field = FieldBox("Optional", text=entry["text"], height=dp(42), arabic=True)
        text_field.bind_value(lambda v: entry.__setitem__("text", v))
        grid.add_widget(text_field)

        grid.add_widget(
            make_control(
                entry, "sv", ("sv", "Show the address / number", "enum", [("", "Design"), ("1", "Show"), ("0", "Hide")])
            )
        )
        if len(entry["values"]) > 1:
            grid.add_widget(
                make_control(
                    entry, "group", ("group", "Several values", "enum", [(1, "One card"), (0, "Separate cards")])
                )
            )

        def featured(value):
            for other in app.entries:
                other["featured"] = 0
            entry["featured"] = value

        seg_box = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(64), spacing=dp(4))
        seg_box.add_widget(make_label("Featured (main) card", size="12sp", height=dp(18)))
        seg_box.add_widget(
            Segmented(
                ["Off", "On"],
                "On" if entry["featured"] else "Off",
                on_select=lambda t: featured(1 if t == "On" else 0),
                height=dp(42),
            )
        )
        grid.add_widget(seg_box)

        for spec in ENTRY_STYLE_SPECS:
            grid.add_widget(make_control(entry["style"], spec[0], spec))

        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(grid)
        box.add_widget(scroll)
        box.add_widget(RoundedButton(text="Done", bg=ACCENT, height=dp(46), on_release=self.dismiss))
        self.content = box


class EntryRow(BoxLayout):
    """One link card in the editor: its values, an optional display name, order buttons."""

    def __init__(self, app, index, **kw):
        super().__init__(orientation="vertical", size_hint_y=None, spacing=dp(6), padding=dp(10), **kw)
        self.bind(minimum_height=self.setter("height"))
        paint(self, SURFACE2, dp(12))
        entry = app.entries[index]
        heading = entry["id"] == "_h"

        head = BoxLayout(size_hint_y=None, height=dp(36), spacing=dp(6))
        head.add_widget(
            make_label("Section title" if heading else entry["name"], size="14sp", color=TEXT, bold=True, height=dp(36))
        )
        for text, callback in (
            ("^", lambda *_: app.move_entry(index, -1)),
            ("v", lambda *_: app.move_entry(index, 1)),
            ("x", lambda *_: app.remove_entry(index)),
        ):
            head.add_widget(
                RoundedButton(
                    text=text,
                    bg=SURFACE,
                    fg=MUTED,
                    size_hint_x=None,
                    width=dp(40),
                    height=dp(34),
                    font_size="13sp",
                    on_release=callback,
                )
            )
        self.add_widget(head)

        if heading:
            field = FieldBox("Heading text", text=entry["title"], height=dp(42), arabic=True)
            field.bind_value(lambda v: entry.__setitem__("title", v))
            self.add_widget(field)
            return

        hint = FIELD_HINTS.get(entry["name"], ("", MULTI_FIELD_HINT))[1]
        many = len(entry["values"]) > 1
        for n, value in enumerate(entry["values"]):
            line = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
            field = FieldBox(hint, text=value, height=dp(42))
            field.input.bind(text=lambda _i, v, n=n: entry["values"].__setitem__(n, v))
            line.add_widget(field)
            if many:
                label = FieldBox("Label", text=entry["labels"][n], height=dp(42), size_hint_x=0.5, arabic=True)
                label.bind_value(lambda v, n=n: entry["labels"].__setitem__(n, v))
                line.add_widget(label)
            self.add_widget(line)

        title = FieldBox(f"Display name (default: {entry['name']})", text=entry["title"], height=dp(42), arabic=True)
        title.bind_value(lambda v: entry.__setitem__("title", v))
        self.add_widget(title)

        actions = BoxLayout(size_hint_y=None, height=dp(38), spacing=dp(6))
        if len(entry["values"]) < MAX_VALUES:
            actions.add_widget(
                RoundedButton(
                    text="+ Another",
                    bg=SURFACE,
                    height=dp(38),
                    font_size="12sp",
                    on_release=lambda *_: app.add_value(index),
                )
            )
        if many:
            actions.add_widget(
                RoundedButton(
                    text="- Last",
                    bg=SURFACE,
                    fg=MUTED,
                    height=dp(38),
                    font_size="12sp",
                    on_release=lambda *_: app.remove_value(index),
                )
            )
        actions.add_widget(
            RoundedButton(
                text="Card options",
                bg=SURFACE,
                height=dp(38),
                font_size="12sp",
                on_release=lambda *_: EntryStylePopup(app, index).open(),
            )
        )
        self.add_widget(actions)


class ProjectsPopup(Popup):
    """Save, load, delete, export and import whole pages (links + texts + design)."""

    def __init__(self, app, **kw):
        super().__init__(**kw)
        self.app = app
        self.title = "Projects"
        self.title_color = TEXT
        self.background = ""
        self.background_color = SURFACE
        self.separator_color = ACCENT
        self.size_hint = (0.96, 0.9)

        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        box.add_widget(make_section("Project name"))
        self.name_field = FieldBox("e.g. Boujlida Store", text=app.project_name, height=dp(42))
        box.add_widget(self.name_field)

        row = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(6))
        row.add_widget(RoundedButton(text="Save", bg=ACCENT, height=dp(44), on_release=self._save))
        row.add_widget(
            RoundedButton(text="Export file", bg=SURFACE2, height=dp(44), font_size="13sp", on_release=self._export)
        )
        row.add_widget(
            RoundedButton(text="Import file", bg=SURFACE2, height=dp(44), font_size="13sp", on_release=self._import)
        )
        box.add_widget(row)
        box.add_widget(make_note("Projects stay on this device, inside the app folder.", dp(20)))

        self.list = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
        self.list.bind(minimum_height=self.list.setter("height"))
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(self.list)
        box.add_widget(scroll)
        box.add_widget(RoundedButton(text="Close", bg=SURFACE2, height=dp(44), on_release=self.dismiss))
        self.content = box
        self._refresh()

    def _refresh(self):
        self.list.clear_widgets()
        names = sorted(n for n in self.app.store["projects"] if not n.startswith("_"))
        if not names:
            self.list.add_widget(make_note("No saved projects yet.", dp(24)))
        for name in names:
            line = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
            line.add_widget(make_label(name, size="14sp", color=TEXT, height=dp(42)))
            line.add_widget(
                RoundedButton(
                    text="Load",
                    bg=SURFACE2,
                    size_hint_x=None,
                    width=dp(70),
                    height=dp(42),
                    font_size="13sp",
                    on_release=lambda *_, n=name: self._load(n),
                )
            )
            line.add_widget(
                RoundedButton(
                    text="Delete",
                    bg=SURFACE2,
                    fg=ERROR,
                    size_hint_x=None,
                    width=dp(76),
                    height=dp(42),
                    font_size="13sp",
                    on_release=lambda *_, n=name: self._delete(n),
                )
            )
            self.list.add_widget(line)

    def _name(self):
        return self.name_field.text.strip()[:60]

    def _save(self, *_):
        name = self._name()
        if not name or name.startswith("_"):
            self.app.set_status("Enter a project name first.", ERROR)
            return
        self.app.project_name = name
        self.app.store_project(name)
        self._refresh()
        self.app.set_status(f"Project saved: {name}", SUCCESS)

    def _load(self, name):
        self.app.load_project(name)
        self.name_field.text = name
        self.dismiss()

    def _delete(self, name):
        self.app.store["projects"].pop(name, None)
        self.app.save_store()
        self._refresh()

    def _export(self, *_):
        name = self._name()
        if not name:
            self.app.set_status("Enter a project name first.", ERROR)
            return
        path = os.path.join(get_save_folder(self.app.user_data_dir), _safe_filename(name) + ".qrproj.json")
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.app.project_data(), f, ensure_ascii=False, indent=1)
            self.app.set_status(f"Project exported:\n{path}", SUCCESS)
        except Exception as e:
            self.app.set_status(f"Could not export: {e}", ERROR)

    def _import(self, *_):
        self.app.pick_file("Choose a project file", ["*.json"], self._imported)

    def _imported(self, path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            name = self._name() or os.path.basename(path).split(".")[0]
            self.app.store["projects"][name] = data
            self.app.save_store()
            self.app.load_project(name)
            self.dismiss()
        except Exception as e:
            self.app.set_status(f"Could not import that file: {e}", ERROR)


# =============================================================================
# PAGES ON GITHUB: list, menu editor, online templates
# =============================================================================
def _styled_popup(popup, title, size_hint):
    popup.title = title
    popup.title_color = TEXT
    popup.background = ""
    popup.background_color = SURFACE
    popup.separator_color = ACCENT
    popup.size_hint = size_hint


def add_bi_field(parent, holder_get, key, ar_hint, en_hint, multiline=False):
    """Two fields (Arabic + English) writing holder[key] and holder[key + '_en'].
    `holder_get` returns the dict at the moment of typing, so a reloaded menu is never written into a stale one."""
    height = dp(76) if multiline else dp(44)
    for suffix, hint, arabic in (("", ar_hint, True), ("_en", en_hint, False)):
        field = FieldBox(hint, height=height, text=holder_get().get(key + suffix, ""), arabic=arabic)
        if multiline:
            field.input.multiline = True
            field.input.padding = [0, dp(10), 0, 0]
        field.bind_value(lambda v, k=key + suffix: holder_get().__setitem__(k, v))
        parent.add_widget(field)


class MyPagesPopup(Popup):
    """Pages stored on GitHub: open one to edit it (its link never changes), copy its link, archive or restore it."""

    def __init__(self, app, **kw):
        super().__init__(**kw)
        self.app = app
        _styled_popup(self, "My pages", (0.96, 0.92))
        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        box.add_widget(
            make_note("Opening a page lets you change it. Generate then saves the changes under the same link.", dp(34))
        )
        self.list = GridLayout(cols=1, spacing=dp(8), size_hint_y=None)
        self.list.bind(minimum_height=self.list.setter("height"))
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(self.list)
        box.add_widget(scroll)
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        row.add_widget(RoundedButton(text="Refresh", bg=SURFACE2, height=dp(46), on_release=lambda *_: self._refresh()))
        row.add_widget(RoundedButton(text="Close", bg=SURFACE2, height=dp(46), on_release=self.dismiss))
        box.add_widget(row)
        self.content = box
        self._refresh()

    def _note(self, text, color=MUTED):
        self.list.clear_widgets()
        label = make_note(text, dp(40))
        label.color = color
        self.list.add_widget(label)

    def _refresh(self):
        cfgs = self.app.require_github()
        if not cfgs:
            self.dismiss()
            return
        self.cfg = cfgs[0]
        self._note("Loading...")
        self.app.run_bg(lambda: index_load(self.cfg), self._loaded)

    def _loaded(self, index, error):
        if error:
            self._note(error, ERROR)
            return
        self.list.clear_widgets()
        items = sorted(index["items"].items(), key=lambda kv: kv[1].get("u", 0), reverse=True)
        if not items:
            self._note("No pages yet. Generate a card or a menu stored on GitHub first.")
            return
        for item_id, meta in items:
            archived = bool(meta.get("x"))
            card = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(96), spacing=dp(6), padding=dp(8))
            paint(card, SURFACE2, dp(12))
            kind = "Menu" if meta.get("t") == "menu" else "Card"
            title = (meta.get("n") or "(no name)") + ("   [archived]" if archived else "")
            card.add_widget(make_label(title, size="14sp", color=MUTED if archived else TEXT, bold=True, height=dp(26), arabic=True))
            card.add_widget(make_label(f"{kind}   id: {item_id}", size="11sp", height=dp(16)))
            actions = BoxLayout(size_hint_y=None, height=dp(34), spacing=dp(6))
            for text, callback, fg in (
                ("Edit", lambda *_, i=item_id: self._edit(i), TEXT),
                ("Copy link", lambda *_, i=item_id: self._copy(i), TEXT),
                ("Restore" if archived else "Archive", lambda *_, i=item_id, a=archived: self._archive(i, not a), MUTED),
            ):
                actions.add_widget(RoundedButton(text=text, bg=SURFACE, fg=fg, height=dp(34), font_size="12sp", on_release=callback))
            card.add_widget(actions)
            self.list.add_widget(card)

    def _edit(self, item_id):
        self.dismiss()
        self.app.load_item(item_id)

    def _copy(self, item_id):
        Clipboard.copy(page_link(self.app._page_base() or DEFAULT_GITHUB, item_id))
        self.app.set_status("Page link copied.", SUCCESS)

    def _archive(self, item_id, archived):
        self._note("Working...")

        def done(_result, error):
            if error:
                self.app.set_status(error, ERROR)
            self._refresh()

        self.app.run_bg(lambda: archive_item(self.cfg, item_id, archived), done)


class OnlineTemplatesPopup(Popup):
    """Design templates stored in the templates repository: unlimited, shared by all your devices."""

    def __init__(self, app, design_popup, **kw):
        super().__init__(**kw)
        self.app = app
        self.design_popup = design_popup
        _styled_popup(self, "Online templates", (0.92, 0.8))
        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        self.list = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
        self.list.bind(minimum_height=self.list.setter("height"))
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(self.list)
        box.add_widget(scroll)
        box.add_widget(RoundedButton(text="Close", bg=SURFACE2, height=dp(46), on_release=self.dismiss))
        self.content = box
        cfgs = app.require_github()
        if not cfgs:
            self.dismiss()
            return
        self.cfg = cfgs[2]
        self.list.add_widget(make_note("Loading...", dp(24)))
        app.run_bg(lambda: templates_list(self.cfg), self._loaded)

    def _loaded(self, listing, error):
        self.list.clear_widgets()
        if error or not listing:
            self.list.add_widget(make_note(error or "No templates yet. Use 'Publish template' in the design window.", dp(40)))
            return
        for slug, name in sorted(listing.items(), key=lambda kv: kv[1].lower()):
            self.list.add_widget(
                RoundedButton(
                    text=name, bg=SURFACE2, height=dp(44), font_size="14sp",
                    on_release=lambda *_, s=slug, n=name: self._apply(s, n),
                )
            )  # fmt: skip

    def _apply(self, slug, name):
        def done(design, error):
            if error:
                self.app.set_status(error, ERROR)
                return
            self.app.design = design
            self.design_popup._show_tab()
            self.app.set_status(f"Template applied: {name}", SUCCESS)
            self.dismiss()

        self.app.run_bg(lambda: template_fetch(self.cfg, slug), done)


class MenuItemRow(BoxLayout):
    """One dish / product: names, description, price, photo, availability."""

    def __init__(self, app, si, ii, **kw):
        super().__init__(orientation="vertical", size_hint_y=None, spacing=dp(6), padding=dp(8), **kw)
        self.bind(minimum_height=self.setter("height"))
        paint(self, SURFACE, dp(10))
        item = app.menu["sections"][si]["items"][ii]

        head = BoxLayout(size_hint_y=None, height=dp(32), spacing=dp(6))
        head.add_widget(make_label(item["name"] or item["name_en"] or "New item", size="13sp", color=TEXT, bold=True, height=dp(32), arabic=True))
        for text, callback in (
            ("^", lambda *_: app.menu_move_item(si, ii, -1)),
            ("v", lambda *_: app.menu_move_item(si, ii, 1)),
            ("x", lambda *_: app.menu_remove_item(si, ii)),
        ):
            head.add_widget(RoundedButton(text=text, bg=SURFACE2, fg=MUTED, size_hint_x=None, width=dp(38), height=dp(32), font_size="13sp", on_release=callback))
        self.add_widget(head)

        add_bi_field(self, lambda: item, "name", "الاسم بالعربية", "Name in English")
        price = FieldBox("Price (e.g. 650)", text=item["price"], height=dp(44))
        price.bind_value(lambda v: item.__setitem__("price", v))
        self.add_widget(price)
        add_bi_field(self, lambda: item, "desc", "الوصف بالعربية (اختياري)", "Description in English (optional)", multiline=True)

        row = BoxLayout(size_hint_y=None, height=dp(40), spacing=dp(6))
        if item["img"]:
            photo_text = "Photo: " + os.path.basename(item["img"])[:18]
        elif item["img_url"]:
            photo_text = "Photo: online"
        else:
            photo_text = "Add photo"
        row.add_widget(RoundedButton(text=photo_text, bg=SURFACE2, height=dp(40), font_size="12sp", on_release=lambda *_: app.menu_pick_photo(item)))
        if item["img"] or item["img_url"]:
            row.add_widget(RoundedButton(text="No photo", bg=SURFACE2, fg=MUTED, size_hint_x=None, width=dp(86), height=dp(40), font_size="12sp", on_release=lambda *_: app.menu_clear_photo(item)))
        self.add_widget(row)

        self.add_widget(
            Segmented(
                ["Available", "Sold out"],
                "Sold out" if item["off"] else "Available",
                on_select=lambda t: item.__setitem__("off", 1 if t == "Sold out" else 0),
                height=dp(38),
            )
        )


class MenuSectionRow(BoxLayout):
    """A menu section (for example Drinks) with its dishes."""

    def __init__(self, app, si, **kw):
        super().__init__(orientation="vertical", size_hint_y=None, spacing=dp(8), padding=dp(10), **kw)
        self.bind(minimum_height=self.setter("height"))
        paint(self, SURFACE2, dp(12))
        section = app.menu["sections"][si]

        head = BoxLayout(size_hint_y=None, height=dp(36), spacing=dp(6))
        head.add_widget(make_label(f"Section {si + 1}", size="14sp", color=TEXT, bold=True, height=dp(36)))
        for text, callback in (
            ("^", lambda *_: app.menu_move_section(si, -1)),
            ("v", lambda *_: app.menu_move_section(si, 1)),
            ("x", lambda *_: app.menu_remove_section(si)),
        ):
            head.add_widget(RoundedButton(text=text, bg=SURFACE, fg=MUTED, size_hint_x=None, width=dp(40), height=dp(34), font_size="13sp", on_release=callback))
        self.add_widget(head)

        add_bi_field(self, lambda: section, "title", "عنوان القسم بالعربية", "Section title in English")
        for ii in range(len(section["items"])):
            self.add_widget(MenuItemRow(app, si, ii))
        self.add_widget(RoundedButton(text="+ Add item", bg=SURFACE, height=dp(40), font_size="13sp", on_release=lambda *_: app.menu_add_item(si)))


# =============================================================================
# SETTINGS POPUP
# =============================================================================
class SettingsPopup(Popup):
    def __init__(self, app, **kwargs):
        super().__init__(**kwargs)
        self.app = app
        self.title = "Settings"
        self.title_color = TEXT
        self.background = ""
        self.background_color = SURFACE
        self.separator_color = ACCENT
        self.size_hint = (0.95, None) if app.is_narrow else (0.55, None)
        self.height = dp(580)

        layout = BoxLayout(orientation="vertical", padding=dp(14), spacing=dp(10))

        layout.add_widget(make_section("GitHub pages address (repository c)"))
        self.url_input = FieldBox(DEFAULT_GITHUB, text=app.github_url)
        layout.add_widget(self.url_input)
        layout.add_widget(
            make_note("The page that opens after scanning. It must contain index.html. Example: https://fennecsys.github.io/c/", dp(34))
        )

        layout.add_widget(make_section("Pages repository (owner/repo, empty = from the address)"))
        self.repo_input = FieldBox(derive_repo(app.github_url) or "owner/repo", text=app.gh_repo)
        layout.add_widget(self.repo_input)

        layout.add_widget(make_section("Pictures repository (owner/repo, empty = owner/a)"))
        self.assets_input = FieldBox(f"{GH_USER}/{REPO_ASSETS}", text=app.gh_assets)
        layout.add_widget(self.assets_input)

        layout.add_widget(make_section("GitHub token (write access to that repository)"))
        self.token_input = FieldBox("github_pat_...", text=app.gh_token)
        self.token_input.input.password = True
        layout.add_widget(self.token_input)
        layout.add_widget(
            make_note(
                "One token for the three repositories (c, a, t), permission Contents: read and write. It stays on this device.",
                dp(34),
            )
        )
        layout.add_widget(Label(size_hint_y=1))  # spacer

        buttons = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(10))
        buttons.add_widget(RoundedButton(text="Cancel", bg=SURFACE2, on_release=self.dismiss))
        buttons.add_widget(RoundedButton(text="Save", bg=ACCENT, on_release=self.save_settings))
        layout.add_widget(buttons)
        self.content = layout

    def save_settings(self, *_):
        url = self.url_input.text.strip()
        if url:
            self.app.github_url = url
        self.app.gh_repo = self.repo_input.text.strip()
        self.app.gh_assets = self.assets_input.text.strip()
        self.app.gh_token = self.token_input.text.strip()
        self.app.save_config()
        self.dismiss()
        self.app.set_status("Settings saved.", SUCCESS)


# =============================================================================
# MAIN APPLICATION
# =============================================================================
def _choice(value, allowed, default):
    """`value` when it is one of `allowed`, otherwise `default` (guards against a stale settings file)."""
    return value if value in allowed else default


def _safe_filename(text):
    """Letters, digits, '_' and '-' only; falls back to 'My_QR'."""
    cleaned = "".join(c for c in (text.strip() or "My_QR") if c.isalnum() or c in "_-")
    return cleaned or "My_QR"


class QRGeneratorApp(App):
    # ---------- start-up ----------
    def build(self):
        self.title = "QR Studio"
        Window.clearcolor = BG
        if IS_MOBILE:
            Window.softinput_mode = "below_target"
        else:
            Window.size = (1180, 860)
            Window.minimum_width, Window.minimum_height = 420, 600

        # user choices (some are overwritten by load_config)
        self.selected_platform = DEFAULT_PLATFORM
        self.github_url = DEFAULT_GITHUB
        self.logo_choice = LOGO_CHOICES[0]
        self.link_type = LINK_TYPES[0]
        self.size_mm = DEFAULT_SIZE_MM
        self.mode = MODE_SINGLE
        self.gh_repo = ""
        self.gh_token = ""
        self.page_logo = None
        self.entries = []  # link cards and section titles of the All-in-one page
        self.texts = clean_texts(None)
        self.design = clean_design(None)
        self.design_name = ""
        self.project_name = ""
        self.gh_assets = ""
        self.storage = STORE_GITHUB  # All in one: page data on GitHub (editable) or inside the link
        self.menu = new_menu()
        self.page_logo_url = ""  # logo already uploaded to the pictures repository
        self.bg_local = None  # background picture chosen but not uploaded yet
        self.item_ids = {MODE_ALL: "", MODE_MENU: ""}  # GitHub page being edited, per mode
        self.page_bar_labels = {}
        self.logo_labels = []
        self.offline_kind = OFFLINE_TYPES[0]
        self.offline_values = {}

        # runtime state
        self.is_narrow = None
        self._busy = False
        self._last_png = self._last_svg = self._last_content = self._last_folder = None

        self.config_path = os.path.join(self.user_data_dir, "settings.json")
        self.store_path = os.path.join(self.user_data_dir, PROJECTS_FILE)
        self.store = load_store(self.store_path)
        self.load_config()
        saved_menu = self.store["projects"].get("_menu")
        if isinstance(saved_menu, dict):
            self.menu = clean_menu(saved_menu.get("menu"))
            self.page_logo_url = self.page_logo_url or _text(saved_menu.get("logo_url"), 300)
            if re.match(r"^[a-z0-9]{4,24}$", str(saved_menu.get("item_id", ""))):
                self.item_ids[MODE_MENU] = saved_menu["item_id"]
        request_android_permissions()

        self.root_holder = BoxLayout(orientation="horizontal")
        self._build_controls()
        self._build_result()

        self.set_mode(MODE_SINGLE)
        self.select_platform(self.selected_platform)
        if "_last" in self.store["projects"]:
            self.load_project("_last", quiet=True)
        self._fill_menu_fields()
        self._show_logo_state()
        self._refresh_page_bars()

        Window.bind(size=lambda *_: self._apply_layout())
        self._apply_layout()
        return self.root_holder

    # ---------- controls column ----------
    def _build_controls(self):
        self.left_layout = BoxLayout(orientation="vertical", spacing=dp(14), size_hint_y=None)
        self.left_layout.bind(minimum_height=self.left_layout.setter("height"))

        self.left_layout.add_widget(self._build_header())

        self.mode_seg = Segmented(
            list(MODE_LABELS.values()),
            MODE_LABELS[MODE_SINGLE],
            on_select=lambda label: self.set_mode(LABEL_TO_MODE[label]),
            height=dp(46),
        )
        self.left_layout.add_widget(self.mode_seg)

        self.body_holder = BoxLayout(orientation="vertical", size_hint_y=None)
        self.body_holder.bind(minimum_height=self.body_holder.setter("height"))
        self.left_layout.add_widget(self.body_holder)

        self._build_single_card()
        self._build_all_card()
        self._build_menu_card()
        self._build_offline_card()
        self.left_layout.add_widget(self._build_output_card())
        self.left_layout.add_widget(self._build_action_row())

    def _build_header(self):
        header = BoxLayout(size_hint_y=None, height=dp(58), spacing=dp(10))
        titles = BoxLayout(orientation="vertical")
        titles.add_widget(make_label("QR Studio", size="22sp", bold=True, color=TEXT, height=dp(30)))
        titles.add_widget(make_label("Clean codes for laser engraving and print", size="12sp", height=dp(20)))
        header.add_widget(titles)
        header.add_widget(
            RoundedButton(
                text="Settings",
                bg=SURFACE2,
                fg=TEXT,
                size_hint_x=None,
                width=dp(96),
                height=dp(40),
                font_size="13sp",
                pos_hint={"center_y": 0.5},
                on_release=lambda *_: SettingsPopup(self).open(),
            )
        )
        return header

    def _build_single_card(self):
        card = self.single_card = Card("Platform")

        self.tile_grid = GridLayout(
            cols=7, spacing=dp(8), size_hint_y=None, row_default_height=dp(76), row_force_default=True
        )
        self.tile_grid.bind(minimum_height=self.tile_grid.setter("height"))
        self.tiles = {}
        for name in PLATFORMS:
            tile = LogoTile(name, name)
            tile.bind(on_release=self.on_tile)
            self.tiles[name] = tile
            self.tile_grid.add_widget(tile)
        card.add_widget(self.tile_grid)

        self.link_label = make_section("Link or username")
        card.add_widget(self.link_label)
        self.url_input = FieldBox(DEFAULT_FIELD_HINT)
        card.add_widget(self.url_input)

        card.add_widget(make_section("Link type"))
        self.link_seg = Segmented(LINK_TYPES, self.link_type, on_select=self._set_link_type)
        card.add_widget(self.link_seg)
        self.link_hint = make_note(LINK_HINTS[self.link_type], dp(36))
        card.add_widget(self.link_hint)

        card.add_widget(make_section("Center logo (print only)"))
        self.logo_seg = Segmented(LOGO_CHOICES, self.logo_choice, on_select=self._set_logo)
        card.add_widget(self.logo_seg)

    def _logo_row(self):
        """Logo chooser row (shared by the card and the menu)."""
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        label = make_label("No logo", size="12sp", height=dp(46))
        self.logo_labels.append(label)
        row.add_widget(label)
        row.add_widget(
            RoundedButton(text="Choose", bg=SURFACE2, size_hint_x=None, width=dp(90), height=dp(46), font_size="13sp", on_release=self.pick_page_logo)
        )
        row.add_widget(
            RoundedButton(text="Remove", bg=SURFACE2, fg=MUTED, size_hint_x=None, width=dp(90), height=dp(46), font_size="13sp", on_release=lambda *_: self._set_page_logo(None))
        )
        return row

    def _page_bar(self, mode):
        """'Editing page xxxx' + My pages / New buttons (cards and menus stored on GitHub)."""
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        label = make_label("", size="12sp", color=TEXT, height=dp(46))
        self.page_bar_labels[mode] = label
        row.add_widget(label)
        row.add_widget(
            RoundedButton(text="My pages", bg=SURFACE2, size_hint_x=None, width=dp(104), height=dp(46), font_size="13sp", on_release=lambda *_: MyPagesPopup(self).open())
        )
        row.add_widget(
            RoundedButton(text="New", bg=SURFACE2, fg=MUTED, size_hint_x=None, width=dp(66), height=dp(46), font_size="13sp", on_release=lambda *_: self.new_page())
        )
        return row

    def _refresh_page_bars(self):
        for mode, label in self.page_bar_labels.items():
            if mode == MODE_ALL and self.storage == STORE_LINK:
                label.text = "Data is inside the link: it cannot be edited after engraving."
            elif self.item_ids.get(mode):
                label.text = f"Editing page {self.item_ids[mode]}. The link and the NFC tag stay the same."
            else:
                label.text = "New page: a fixed link is created when you press Generate."

    def _text_field(self, card, key, hint, arabic, multiline=False):
        """Field writing into self.texts[key] (always the current dict)."""
        field = FieldBox(hint, height=dp(84) if multiline else None, arabic=arabic)
        if multiline:
            field.input.multiline = True
            field.input.padding = [0, dp(12), 0, 0]
        field.bind_value(lambda v, k=key: self.texts.__setitem__(k, v))
        card.add_widget(field)
        return field

    def _build_all_card(self):
        card = self.all_card = Card("Your links")

        card.add_widget(self._page_bar(MODE_ALL))
        card.add_widget(make_section("Where the page data is kept"))
        self.store_seg = Segmented(STORES, self.storage, on_select=self._set_storage)
        card.add_widget(self.store_seg)
        card.add_widget(
            make_note("GitHub: the code stays the same and you can edit the page later. In link: nothing is uploaded.", dp(34))
        )

        card.add_widget(make_section("Name shown on the page (optional)"))
        self.account_input = FieldBox("الاسم بالعربية / Your name", arabic=True)
        card.add_widget(self.account_input)
        self.account_en = self._text_field(card, "name_en", "Name in English (optional)", False)

        card.add_widget(make_section("Language the page opens in"))
        self.lang_seg = Segmented(list(LANG_CHOICES), "Auto", on_select=lambda t: self.texts.__setitem__("lang", LANG_CHOICES[t]))
        card.add_widget(self.lang_seg)

        card.add_widget(make_section("Page logo (optional)"))
        card.add_widget(self._logo_row())
        card.add_widget(
            make_note("Shown on your page after scanning. It is uploaded to your GitHub pictures repository and does not change the QR code size.", dp(34))
        )

        card.add_widget(make_section("Page design"))
        design_row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        for text, callback in (
            ("Design", lambda *_: DesignPopup(self).open()),
            ("Projects", lambda *_: ProjectsPopup(self).open()),
            ("Preview", lambda *_: self.preview_in_browser()),
        ):
            design_row.add_widget(RoundedButton(text=text, bg=SURFACE2, height=dp(46), font_size="13sp", on_release=callback))
        card.add_widget(design_row)

        card.add_widget(make_section("Welcome texts (optional): Arabic, then English"))
        self.hint_input = self._text_field(card, "hint", "السطر تحت الاسم", True)
        self.hint_en = self._text_field(card, "hint_en", "Line under the name", False)
        self.intro_input = self._text_field(card, "intro", "العنوان، أوقات العمل...", True, multiline=True)
        self.intro_en = self._text_field(card, "intro_en", "Address, opening hours...", False, multiline=True)
        self.footer_input = self._text_field(card, "footer", "نص أسفل الصفحة", True)
        self.footer_en = self._text_field(card, "footer_en", "Footer text", False)
        card.add_widget(make_section("Save-contact button"))
        self.vcard_seg = Segmented(["Off", "On"], "Off", on_select=lambda t: self.texts.__setitem__("vcard", 1 if t == "On" else 0))
        card.add_widget(self.vcard_seg)

        card.add_widget(make_section("Add a link"))
        self.add_grid = GridLayout(cols=4, spacing=dp(8), size_hint_y=None, row_default_height=dp(76), row_force_default=True)
        self.add_grid.bind(minimum_height=self.add_grid.setter("height"))
        for name in PLATFORMS:
            tile = LogoTile(name, name)
            tile.bind(on_release=lambda t: self.add_entry(t.key))
            self.add_grid.add_widget(tile)
        card.add_widget(self.add_grid)
        card.add_widget(
            RoundedButton(text="+ Section title", bg=SURFACE2, fg=MUTED, height=dp(40), font_size="13sp", on_release=self.add_heading)
        )

        self.entries_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.entries_box.bind(minimum_height=self.entries_box.setter("height"))
        card.add_widget(self.entries_box)
        self._render_entries()

    # ---------- menu card ----------
    def _menu_field(self, card, key, hint, arabic):
        field = FieldBox(hint, arabic=arabic)
        field.bind_value(lambda v, k=key: self.menu.__setitem__(k, v))
        card.add_widget(field)
        self.menu_fields[key] = field

    def _build_menu_card(self):
        card = self.menu_card = Card("Menu")
        self.menu_fields = {}

        card.add_widget(self._page_bar(MODE_MENU))
        card.add_widget(make_note("Stored on GitHub: change prices or mark dishes as sold out any time. The code never changes.", dp(34)))

        card.add_widget(make_section("Restaurant / shop name"))
        self._menu_field(card, "name", "الاسم بالعربية", True)
        self._menu_field(card, "name_en", "Name in English", False)

        card.add_widget(make_section("Language the menu opens in"))
        self.menu_lang_seg = Segmented(list(LANG_CHOICES), "Auto", on_select=lambda t: self.menu.__setitem__("lang", LANG_CHOICES[t]))
        card.add_widget(self.menu_lang_seg)

        card.add_widget(make_section("Logo (optional)"))
        card.add_widget(self._logo_row())

        card.add_widget(make_section("Design"))
        design_row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        for text, callback in (
            ("Design", lambda *_: DesignPopup(self).open()),
            ("Open page", lambda *_: self.open_current_page()),
        ):
            design_row.add_widget(RoundedButton(text=text, bg=SURFACE2, height=dp(46), font_size="13sp", on_release=callback))
        card.add_widget(design_row)

        card.add_widget(make_section("Line under the name (optional)"))
        self._menu_field(card, "hint", "سطر تحت الاسم", True)
        self._menu_field(card, "hint_en", "Line under the name", False)

        card.add_widget(make_section("Currency shown after prices"))
        self._menu_field(card, "currency", "دج", True)
        self._menu_field(card, "currency_en", "DA", False)

        card.add_widget(make_section("Call and WhatsApp buttons (optional)"))
        self._menu_field(card, "phone", "Phone: +213 555 12 34 56", False)
        self._menu_field(card, "whatsapp", "WhatsApp: +213 555 12 34 56", False)

        card.add_widget(make_section("Text at the bottom (optional)"))
        self._menu_field(card, "footer", "نص أسفل الصفحة", True)
        self._menu_field(card, "footer_en", "Footer text", False)

        card.add_widget(make_section("Sections and items"))
        self.menu_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.menu_box.bind(minimum_height=self.menu_box.setter("height"))
        card.add_widget(self.menu_box)
        card.add_widget(RoundedButton(text="+ Add section", bg=SURFACE2, height=dp(44), font_size="13sp", on_release=lambda *_: self.menu_add_section()))
        self._render_menu()

    def _fill_menu_fields(self):
        for key, field in self.menu_fields.items():
            field.text = self.menu.get(key, "")
        self.menu_lang_seg.select(self._lang_label(self.menu.get("lang", "")), notify=False)

    @staticmethod
    def _lang_label(code):
        return next((label for label, value in LANG_CHOICES.items() if value == code), "Auto")

    def _render_menu(self):
        self.menu_box.clear_widgets()
        for si in range(len(self.menu["sections"])):
            self.menu_box.add_widget(MenuSectionRow(self, si))

    # ---------- offline card ----------
    def _build_offline_card(self):
        card = self.offline_card = Card("Offline code")
        card.add_widget(make_note("The data is inside the code: it works without internet, but it cannot be changed after engraving.", dp(34)))
        grid = GridLayout(cols=3, spacing=dp(8), size_hint_y=None, row_default_height=dp(44), row_force_default=True)
        grid.bind(minimum_height=grid.setter("height"))
        self.offline_buttons = {}
        for kind in OFFLINE_TYPES:
            button = RoundedButton(text=kind, bg=SURFACE2, fg=MUTED, height=dp(44), font_size="13sp", on_release=lambda *_, k=kind: self.select_offline(k))
            self.offline_buttons[kind] = button
            grid.add_widget(button)
        card.add_widget(grid)
        self.offline_note = make_note("", dp(34))
        card.add_widget(self.offline_note)
        self.offline_box = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_y=None)
        self.offline_box.bind(minimum_height=self.offline_box.setter("height"))
        card.add_widget(self.offline_box)
        self.select_offline(self.offline_kind)

    def select_offline(self, kind):
        self.offline_kind = kind
        for name, button in self.offline_buttons.items():
            selected = name == kind
            button.set_bg(ACCENT if selected else SURFACE2)
            button.color = TEXT if selected else MUTED
        self.offline_note.text = OFFLINE_NOTES[kind]
        self.offline_box.clear_widgets()
        values = self.offline_values.setdefault(kind, {})
        for key, label, hint, style in OFFLINE_FIELDS[kind]:
            self.offline_box.add_widget(make_section(label))
            field = FieldBox(hint, text=values.get(key, ""), height=dp(84) if style == "m" else None, arabic=style in ("a", "m"))
            if style == "m":
                field.input.multiline = True
                field.input.padding = [0, dp(12), 0, 0]
            field.bind_value(lambda v, k=key, d=values: d.__setitem__(k, v))
            self.offline_box.add_widget(field)

    def _build_output_card(self):
        card = Card("Output")
        card.add_widget(make_label("File name", size="12sp", height=dp(18)))
        self.name_input = FieldBox("My_QR")
        card.add_widget(self.name_input)
        card.add_widget(make_label("Code width in mm (SVG)", size="12sp", height=dp(18)))
        self.size_input = FieldBox("40", text=f"{self.size_mm:g}")
        card.add_widget(self.size_input)
        card.add_widget(make_note("Leave about 4 squares of free space around the code on the material.", dp(34)))
        return card

    def _build_action_row(self):
        row = BoxLayout(size_hint_y=None, height=dp(54), spacing=dp(10))
        row.add_widget(
            RoundedButton(
                text="Clear", bg=SURFACE2, fg=MUTED, size_hint_x=0.32, height=dp(54), on_release=self.clear_form
            )
        )
        self.gen_btn = RoundedButton(
            text="Generate QR", bg=ACCENT, size_hint_x=0.68, height=dp(54), font_size="16sp", on_release=self.generate
        )
        row.add_widget(self.gen_btn)
        return row

    # ---------- result column ----------
    def _build_result(self):
        self.right_layout = BoxLayout(orientation="vertical", spacing=dp(14), size_hint_y=None)
        self.right_layout.bind(minimum_height=self.right_layout.setter("height"))

        card = Card("Result")

        self.preview_holder = FloatLayout(size_hint_y=None, height=dp(340))
        paint(self.preview_holder, (1, 1, 1, 1), dp(12))
        self.preview = KivyImage(
            fit_mode="contain", nocache=True, size_hint=(0.9, 0.9), pos_hint={"center_x": 0.5, "center_y": 0.5}
        )
        self.preview_hint = Label(text="Your QR code will appear here", color=rgba("#7A869E"), font_size="13sp")
        self.preview_holder.add_widget(self.preview_hint)
        self.preview_holder.add_widget(self.preview)
        card.add_widget(self.preview_holder)

        stats = BoxLayout(size_hint_y=None, height=dp(56), spacing=dp(8))
        self.stat_modules = Stat("Squares")
        self.stat_size = Stat("Square size")
        self.stat_margin = Stat("Free margin")
        for stat in self._stats():
            stats.add_widget(stat)
        card.add_widget(stats)

        self.content_label = make_note("", dp(34))
        card.add_widget(self.content_label)
        card.add_widget(self._build_result_actions())

        self.status = Label(
            text="Ready.", font_size="13sp", color=MUTED, size_hint_y=None, height=dp(72), halign="left", valign="top"
        )
        _fit_text(self.status)
        card.add_widget(self.status)

        self.right_layout.add_widget(card)

    def _build_result_actions(self):
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))

        def action(text, callback):
            row.add_widget(RoundedButton(text=text, bg=SURFACE2, height=dp(46), font_size="13sp", on_release=callback))

        action("Copy link", self.copy_link)
        if IS_ANDROID:
            action("Share PNG", lambda *_: self.share("png"))
            action("Share SVG", lambda *_: self.share("svg"))
        else:
            action("Open folder", self.open_output_folder)
        return row

    def _stats(self):
        return (self.stat_modules, self.stat_size, self.stat_margin)

    # ---------- responsive layout ----------
    def _apply_layout(self):
        narrow = IS_MOBILE or Window.width < dp(NARROW_WIDTH_DP) or Window.width < Window.height * 1.2
        self.tile_grid.cols = 4 if narrow else 7
        self.add_grid.cols = 4 if narrow else 7
        self.preview_holder.height = min(max(Window.width - dp(70), dp(220)), dp(340)) if narrow else dp(340)

        if narrow == self.is_narrow:
            return
        self.is_narrow = narrow

        for layout in (self.left_layout, self.right_layout):
            if layout.parent:
                layout.parent.remove_widget(layout)
        self.root_holder.clear_widgets()

        if narrow:
            self._layout_single_column()
        else:
            self._layout_two_columns()

    def _layout_single_column(self):
        self.root_holder.padding = dp(12)
        self.root_holder.spacing = dp(10)
        column = BoxLayout(orientation="vertical", spacing=dp(14), size_hint_y=None)
        column.bind(minimum_height=column.setter("height"))
        column.add_widget(self.left_layout)
        column.add_widget(self.right_layout)
        scroll = ScrollView(bar_width=dp(4), do_scroll_x=False)
        scroll.add_widget(column)
        self.root_holder.add_widget(scroll)

    def _layout_two_columns(self):
        self.root_holder.padding = dp(22)
        self.root_holder.spacing = dp(22)
        for layout, share in ((self.left_layout, 0.58), (self.right_layout, 0.42)):
            scroll = ScrollView(size_hint_x=share, bar_width=dp(6), do_scroll_x=False)
            scroll.add_widget(layout)
            self.root_holder.add_widget(scroll)

    # ---------- config ----------
    # (load_config deliberately keeps its name: it replaces Kivy's App.load_config)
    def load_config(self):
        try:
            if not os.path.exists(self.config_path):
                return
            with open(self.config_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.github_url = data.get("github_url", DEFAULT_GITHUB)
            if self.github_url.strip() == OLD_DEFAULT_GITHUB:
                self.github_url = DEFAULT_GITHUB
            self.storage = _choice(data.get("storage", STORE_GITHUB), STORES, STORE_GITHUB)
            self.gh_assets = data.get("gh_assets", "")
            self.size_mm = float(data.get("size_mm", DEFAULT_SIZE_MM))
            self.link_type = _choice(data.get("link_type", "Auto"), LINK_TYPES, "Auto")
            self.logo_choice = _choice(data.get("logo_choice", "No logo"), LOGO_CHOICES, "No logo")
            self.selected_platform = _choice(data.get("platform", DEFAULT_PLATFORM), PLATFORMS, DEFAULT_PLATFORM)
            self.gh_repo = data.get("gh_repo", "")
            self.gh_token = data.get("gh_token", "")
        except Exception as e:
            print(f"Error loading config: {e}")

    def save_config(self):
        try:
            with open(self.config_path, "w", encoding="utf-8") as f:
                json.dump(
                    {
                        "github_url": self.github_url,
                        "size_mm": self.size_mm,
                        "link_type": self.link_type,
                        "logo_choice": self.logo_choice,
                        "platform": self.selected_platform,
                        "gh_repo": self.gh_repo,
                        "gh_assets": self.gh_assets,
                        "storage": self.storage,
                        "gh_token": self.gh_token,
                    },
                    f,
                    indent=4,
                )
        except Exception as e:
            print(f"Error saving config: {e}")

    # ---------- small UI actions ----------
    def set_status(self, text, color=MUTED):
        self.status.text = text
        self.status.color = color

    def set_mode(self, mode):
        self.mode = mode
        self.mode_seg.select(MODE_LABELS[mode], notify=False)
        self.body_holder.clear_widgets()
        cards = {
            MODE_SINGLE: self.single_card,
            MODE_ALL: self.all_card,
            MODE_MENU: self.menu_card,
            MODE_OFFLINE: self.offline_card,
        }
        self.body_holder.add_widget(cards[mode])

    def select_platform(self, name):
        self.selected_platform = name
        for platform_name, tile in self.tiles.items():
            tile.set_selected(platform_name == name)
        label, hint = FIELD_HINTS.get(name, (f"{name.upper()} LINK OR USERNAME", DEFAULT_FIELD_HINT))
        self.link_label.text = label
        self.url_input.input.hint_text = hint

    def on_tile(self, tile):
        self.select_platform(tile.key)

    def _set_link_type(self, value):
        self.link_type = value
        self.link_hint.text = LINK_HINTS[value]

    def _set_logo(self, value):
        self.logo_choice = value

    def clear_form(self, *_):
        self.url_input.text = ""
        self.entries = []
        self._render_entries()
        self.texts = clean_texts(None)
        self._fill_card_fields()
        self.account_input.text = ""
        self.menu = new_menu()
        self._fill_menu_fields()
        self._render_menu()
        self.offline_values = {}
        self.select_offline(self.offline_kind)
        self.item_ids = {MODE_ALL: "", MODE_MENU: ""}
        self._refresh_page_bars()
        self.bg_local = None
        self._set_page_logo(None)
        self.name_input.text = ""
        self.preview.source = ""
        self.preview_hint.opacity = 1
        for stat in self._stats():
            stat.set("-")
        self.content_label.text = ""
        self._last_png = self._last_svg = self._last_content = self._last_folder = None
        self.set_status("Cleared. Ready for new input.")

    def copy_link(self, *_):
        if not self._last_content:
            self.set_status("Generate a QR code first.", ERROR)
            return
        Clipboard.copy(self._last_content)
        self.set_status("Link copied.", SUCCESS)

    def open_output_folder(self, *_):
        if not self._last_folder:
            self.set_status("Generate a QR code first.", ERROR)
            return
        if not open_folder(self._last_folder):
            self.set_status(f"Could not open the folder. It is here:\n{self._last_folder}", ERROR)

    def share(self, kind):
        path = self._last_png if kind == "png" else self._last_svg
        if not path or not os.path.isfile(path):
            self.set_status("Generate a QR code first.", ERROR)
            return
        if not share_file(path):
            self.set_status("Sharing is not available. The file is saved on the phone.", ERROR)

    # ---------- background work + GitHub access ----------
    def run_bg(self, work, done):
        """Runs work() off the UI thread, then done(result, error_text) on the UI thread."""

        def runner():
            try:
                result, error = work(), None
            except Exception as e:
                result, error = None, str(e)
            Clock.schedule_once(lambda _dt: done(result, error))

        threading.Thread(target=runner, daemon=True).start()

    def gh_configs(self):
        """(pages, pictures, templates) repository settings."""
        pages_repo = self.gh_repo.strip() or derive_repo(self.github_url)
        owner = pages_repo.split("/")[0] if pages_repo else GH_USER
        assets_repo = self.gh_assets.strip() or f"{owner}/{REPO_ASSETS}"
        token = self.gh_token.strip()
        return (
            {"repo": pages_repo, "token": token, "owner": owner},
            {"repo": assets_repo, "token": token, "owner": assets_repo.split("/")[0]},
            {"repo": f"{owner}/{REPO_TEMPLATES}", "token": token, "owner": owner},
        )

    def require_github(self):
        """The three repository settings, or None (with the reason in the status line)."""
        if not self._page_base():
            self.set_status("Open Settings and enter a valid GitHub page URL.", ERROR)
            return None
        cfgs = self.gh_configs()
        if not cfgs[0]["token"]:
            self.set_status("Add your GitHub token in Settings.", ERROR)
            return None
        if "/" not in cfgs[0]["repo"] or "/" not in cfgs[1]["repo"]:
            self.set_status("Enter the repositories as owner/repo in Settings.", ERROR)
            return None
        return cfgs

    # ---------- pages stored on GitHub ----------
    def new_page(self):
        if self.mode in self.item_ids:
            self.item_ids[self.mode] = ""
        self._refresh_page_bars()
        self.set_status("Next Generate creates a NEW page with a new link.", MUTED)

    def open_current_page(self):
        if not self.item_ids[MODE_MENU]:
            self.set_status("Generate the menu first, then it can be opened here.", ERROR)
            return
        if not open_url(page_link(self._page_base() or DEFAULT_GITHUB, self.item_ids[MODE_MENU])):
            self.set_status("Could not open the browser.", ERROR)

    def load_item(self, item_id):
        cfgs = self.require_github()
        if not cfgs:
            return
        self.set_status("Loading the page...", MUTED)
        self.run_bg(lambda: fetch_item(cfgs[0], item_id), lambda obj, err: self._item_loaded(item_id, obj, err))

    def _item_loaded(self, item_id, obj, error):
        if error:
            self.set_status(error, ERROR)
            return
        self.page_logo = None
        self.bg_local = None
        self.page_logo_url = obj.get("lgu") if isinstance(obj.get("lgu"), str) and IMG_RE.match(obj["lgu"]) else ""
        if obj.get("type") == "menu":
            self.menu, self.design = menu_from_item(obj)
            kind = MODE_MENU
            self._fill_menu_fields()
            self._render_menu()
            self.set_mode(MODE_MENU)
        else:
            name, self.texts = texts_from_item(obj)
            self.entries, self.design = entries_from_item(obj)
            kind = MODE_ALL
            self.storage = STORE_GITHUB
            self.store_seg.select(STORE_GITHUB, notify=False)
            self.account_input.text = name
            self._fill_card_fields()
            self._render_entries()
            self.set_mode(MODE_ALL)
        self.item_ids[kind] = item_id
        self._show_logo_state()
        self._refresh_page_bars()
        self.set_status(f"Page {item_id} loaded. Change it, then press Generate: the link stays the same.", SUCCESS)

    def _fill_card_fields(self):
        t = self.texts
        for field, key in (
            (self.hint_input, "hint"), (self.intro_input, "intro"), (self.footer_input, "footer"),
            (self.account_en, "name_en"), (self.hint_en, "hint_en"), (self.intro_en, "intro_en"), (self.footer_en, "footer_en"),
        ):  # fmt: skip
            field.text = t[key]
        self.vcard_seg.select("On" if t["vcard"] else "Off", notify=False)
        self.lang_seg.select(self._lang_label(t["lang"]), notify=False)

    def _set_storage(self, value):
        self.storage = value
        self._refresh_page_bars()
        self.save_config()

    def set_background_file(self, path):
        self.bg_local = path
        self.set_status("Background picture chosen. It is uploaded when you press Generate.", SUCCESS)

    # ---------- menu editing ----------
    def menu_add_section(self):
        if len(self.menu["sections"]) >= MENU_MAX_SECTIONS:
            self.set_status("Too many sections.", ERROR)
            return
        self.menu["sections"].append(new_menu_section())
        self._render_menu()

    def menu_remove_section(self, si):
        if len(self.menu["sections"]) > 1:
            del self.menu["sections"][si]
        else:
            self.menu["sections"][0] = new_menu_section()
        self._render_menu()

    def menu_move_section(self, si, step):
        sections = self.menu["sections"]
        target = si + step
        if 0 <= target < len(sections):
            sections[si], sections[target] = sections[target], sections[si]
            self._render_menu()

    def menu_add_item(self, si):
        items = self.menu["sections"][si]["items"]
        if len(items) >= MENU_MAX_ITEMS:
            self.set_status("Too many items in one section.", ERROR)
            return
        items.append(new_menu_item())
        self._render_menu()

    def menu_remove_item(self, si, ii):
        items = self.menu["sections"][si]["items"]
        del items[ii]
        if not items:
            items.append(new_menu_item())
        self._render_menu()

    def menu_move_item(self, si, ii, step):
        items = self.menu["sections"][si]["items"]
        target = ii + step
        if 0 <= target < len(items):
            items[ii], items[target] = items[target], items[ii]
            self._render_menu()

    def menu_pick_photo(self, item):
        def chosen(path):
            item["img"] = path
            self._render_menu()

        self.pick_file("Choose a photo", ["*.png", "*.jpg", "*.jpeg", "*.webp"], chosen)

    def menu_clear_photo(self, item):
        item["img"] = ""
        item["img_url"] = ""
        self._render_menu()

    # ---------- links editor (All in one) ----------
    def _render_entries(self):
        self.entries_box.clear_widgets()
        if not self.entries:
            self.entries_box.add_widget(make_note("Tap a platform above to add a link.", dp(24)))
        for index in range(len(self.entries)):
            self.entries_box.add_widget(EntryRow(self, index))

    def add_entry(self, platform_name):
        if len(self.entries) >= MAX_ENTRIES:
            self.set_status("Too many cards on one page.", ERROR)
            return
        self.entries.append(new_entry(platform_name))
        self._render_entries()

    def add_heading(self, *_):
        self.entries.append(new_heading())
        self._render_entries()

    def move_entry(self, index, step):
        target = index + step
        if 0 <= target < len(self.entries):
            self.entries[index], self.entries[target] = self.entries[target], self.entries[index]
            self._render_entries()

    def remove_entry(self, index):
        del self.entries[index]
        self._render_entries()

    def add_value(self, index):
        entry = self.entries[index]
        if len(entry["values"]) < MAX_VALUES:
            entry["values"].append("")
            entry["labels"].append("")
            self._render_entries()

    def remove_value(self, index):
        entry = self.entries[index]
        if len(entry["values"]) > 1:
            entry["values"].pop()
            entry["labels"].pop()
            self._render_entries()

    # ---------- design: preview / online update ----------
    def _page_base(self):
        base = self.github_url.strip().split("#")[0]
        return base if base.startswith("http") else None

    def preview_in_browser(self):
        """Opens the real links page with the current design inside the link (nothing is uploaded).
        The repository's index.html must already be the design-capable version."""
        base = self._page_base()
        if not base:
            self.set_status("Open Settings and enter a valid GitHub page URL.", ERROR)
            return
        try:
            items, design = compile_page(self.entries, self.design)
        except ValueError as e:
            self.set_status(str(e), ERROR)
            return
        if not items:
            self.set_status("Add at least one link to preview.", ERROR)
            return
        payload = build_payload(self.account_input.text.strip(), self.texts, items, design=design)
        if not open_url(base + "#" + encode_payload(payload)):
            self.set_status("Could not open the browser.", ERROR)
        else:
            self.set_status("Preview opened in the browser (logo not shown).", SUCCESS)

    def update_design_online(self):
        """Publishes the current look under the public design name: pages already printed change appearance."""
        name = self.design_name.strip()
        if not name:
            self.set_status("Type a public design name first.", ERROR)
            return
        base = self._check_page_settings(True)
        if base is None or self._busy:
            return
        try:
            _items, design = compile_page(self.entries, self.design)
        except ValueError as e:
            self.set_status(str(e), ERROR)
            return
        cfg = {"repo": self.gh_repo.strip() or derive_repo(self.github_url), "token": self.gh_token.strip()}
        design_id = slugify_design_name(name)
        self._busy = True
        self.set_status("Updating the design...", MUTED)

        def work():
            try:
                github_put_file(
                    cfg,
                    f"{DESIGN_FOLDER}/{design_id}.json",
                    design_json(design),
                    f"Design {design_id}",
                    overwrite=True,
                    what="the design",
                )
                message = (
                    f"Design '{design_id}' updated. It can take a few minutes to appear.\n"
                    "Do not add or remove cards for printed codes: styles follow card positions."
                )
                Clock.schedule_once(lambda _dt: self._design_done(message, SUCCESS))
            except Exception as e:
                text = str(e)
                Clock.schedule_once(lambda _dt: self._design_done(text, ERROR))

        threading.Thread(target=work, daemon=True).start()

    def _design_done(self, message, color):
        self._busy = False
        self.set_status(message, color)

    # ---------- projects ----------
    def project_data(self):
        return {
            "name": self.account_input.text,
            "entries": copy.deepcopy(self.entries),
            "texts": dict(self.texts),
            "design": copy.deepcopy(self.design),
            "design_name": self.design_name,
            "logo": self.page_logo or "",
            "item_id": self.item_ids[MODE_ALL],
        }

    def save_store(self):
        try:
            save_store(self.store_path, self.store)
        except Exception as e:
            print(f"[Projects] save failed: {e}")

    def store_project(self, name):
        self.store["projects"][name] = self.project_data()
        self.save_store()

    def load_project(self, name, quiet=False):
        data = self.store["projects"].get(name)
        if not isinstance(data, dict):
            return
        self.entries = clean_entries(data.get("entries"))
        self.texts = clean_texts(data.get("texts"))
        self.design = clean_design(data.get("design"))
        self.design_name = _text(data.get("design_name"), 40)
        self.account_input.text = _text(data.get("name"), 80)
        self._fill_card_fields()
        self._set_page_logo(data.get("logo") or None)
        # only the automatic draft remembers which GitHub page it belongs to (named projects work as templates)
        item_id = data.get("item_id") if name == "_last" else ""
        self.item_ids[MODE_ALL] = item_id if isinstance(item_id, str) and ITEM_ID_RE.match(item_id) else ""
        if not name.startswith("_"):
            self.project_name = name
        self._render_entries()
        if not quiet:
            self.set_status(f"Project loaded: {name}", SUCCESS)

    def pick_file(self, title, filters, callback):
        """Built-in file browser; calls callback(path) with the chosen file."""
        start = "/storage/emulated/0" if IS_ANDROID else os.path.expanduser("~")
        if not os.path.isdir(start):
            start = os.path.expanduser("~")
        chooser = FileChooserListView(path=start, filters=filters)
        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        box.add_widget(chooser)
        popup = Popup(title=title, content=box, size_hint=(0.95, 0.9))

        def choose(*_):
            if chooser.selection:
                callback(chooser.selection[0])
            popup.dismiss()

        buttons = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(10))
        buttons.add_widget(RoundedButton(text="Cancel", bg=SURFACE2, on_release=popup.dismiss))
        buttons.add_widget(RoundedButton(text="Select", bg=ACCENT, on_release=choose))
        box.add_widget(buttons)
        popup.open()

    # ---------- page logo ----------
    def _logo_text(self, text, color):
        for label in self.logo_labels:
            label.text = text
            label.color = color

    def _show_logo_state(self):
        if self.page_logo:
            self._logo_text(os.path.basename(self.page_logo), TEXT)
        elif self.page_logo_url:
            self._logo_text("Online logo (kept)", TEXT)
        else:
            self._logo_text("No logo", MUTED)

    def _set_page_logo(self, path):
        if path and os.path.isfile(path):
            self.page_logo = path
        else:
            self.page_logo = None
            self.page_logo_url = ""
        self._show_logo_state()

    def pick_page_logo(self, *_):
        if IS_ANDROID:
            try:
                from androidstorage4kivy import Chooser, SharedStorage

                def on_chosen(uris):
                    if not uris:
                        return
                    try:
                        path = SharedStorage().copy_from_shared(uris[0])
                    except Exception as e:
                        print(f"[Logo] copy_from_shared failed: {e}")
                        path = None
                    Clock.schedule_once(lambda _dt: self._set_page_logo(path))

                self._chooser = Chooser(on_chosen)
                self._chooser.choose_content("image/*")
                return
            except Exception as e:
                print(f"[Logo] chooser failed: {e}")
        self._open_logo_popup()

    def _open_logo_popup(self):
        """Built-in file browser (desktop, or Android when the system chooser is unavailable)."""
        start = "/storage/emulated/0" if IS_ANDROID else os.path.expanduser("~")
        if not os.path.isdir(start):
            start = os.path.expanduser("~")
        chooser = FileChooserListView(path=start, filters=["*.png", "*.jpg", "*.jpeg", "*.webp"])
        box = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        box.add_widget(chooser)
        popup = Popup(title="Choose a logo", content=box, size_hint=(0.95, 0.9))

        def choose(*_):
            if chooser.selection:
                self._set_page_logo(chooser.selection[0])
            popup.dismiss()

        buttons = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(10))
        buttons.add_widget(RoundedButton(text="Cancel", bg=SURFACE2, on_release=popup.dismiss))
        buttons.add_widget(RoundedButton(text="Select", bg=ACCENT, on_release=choose))
        box.add_widget(buttons)
        popup.open()

    # ---------- generation (network runs off the UI thread) ----------
    def _check_page_settings(self, needs_upload=False):
        """In-link All-in-one prerequisites. Returns the links page URL (without '#'), or None after
        showing the problem in the status line."""
        base = self.github_url.strip().split("#")[0]
        if not base.startswith("http"):
            self.set_status("Open Settings and enter a valid GitHub page URL.", ERROR)
            return None
        if self.page_logo or needs_upload:
            if not self.gh_token.strip():
                self.set_status("To upload the logo or the design, add your GitHub token in Settings.", ERROR)
                return None
            if not (self.gh_repo.strip() or derive_repo(self.github_url)):
                self.set_status("Enter the GitHub repository (owner/repo) in Settings.", ERROR)
                return None
        return base

    def generate(self, *_):
        if self._busy:
            return
        mode = self.mode

        base_github, items, design, contents = "", [], None, None
        if mode == MODE_ALL:
            try:
                items, design = compile_page(self.entries, self.design)
            except ValueError as e:
                self.set_status(str(e), ERROR)
                return
            if not items:
                self.set_status("Add at least one link.", ERROR)
                return
            if self.storage == STORE_GITHUB:
                if self.require_github() is None:
                    return
                base_github = self._page_base()
            else:
                wants_design = bool(self.design_name.strip()) or not design_is_default(design)
                base_github = self._check_page_settings(wants_design)
                if base_github is None:
                    return
        elif mode == MODE_MENU:
            try:
                compile_menu(self.menu, self.design)
            except ValueError as e:
                self.set_status(str(e), ERROR)
                return
            if self.require_github() is None:
                return
            base_github = self._page_base()
            design = clean_design(self.design)
        elif mode == MODE_OFFLINE:
            try:
                contents = build_offline(self.offline_kind, self.offline_values.get(self.offline_kind, {}))
            except ValueError as e:
                self.set_status(str(e), ERROR)
                return

        try:
            size_mm = float(self.size_input.text.strip().replace(",", "."))
            if size_mm <= 0:
                raise ValueError
        except ValueError:
            self.set_status("Enter a valid code width in mm.", ERROR)
            return
        self.size_mm = size_mm
        self.save_config()
        if mode == MODE_ALL:
            self.store_project("_last")
        elif mode == MODE_MENU:
            self.store_menu()

        pages_mode = mode in (MODE_ALL, MODE_MENU)
        job = {
            "mode": mode,
            "platform": self.selected_platform,
            "raw": self.url_input.text.strip(),
            "items": items,
            "design": design,
            "design_name": self.design_name.strip(),
            "texts": dict(self.texts),
            "name": self.account_input.text.strip(),
            "filename": _safe_filename(self.name_input.text),
            "base_github": base_github,
            "link_type": self.link_type,
            "logo_choice": self.logo_choice,
            "size_mm": size_mm,
            "folder": get_save_folder(self.user_data_dir),
            "user_dir": self.user_data_dir,
            "page_logo": self.page_logo if pages_mode else None,
            "page_logo_url": self.page_logo_url if pages_mode else "",
            "store": self.storage,
            "menu": copy.deepcopy(self.menu) if mode == MODE_MENU else None,
            "bg_local": self.bg_local if pages_mode else None,
            "item_id": self.item_ids.get(mode) or None,
            "contents": contents,
            "cfgs": self.gh_configs(),
            "gh": {
                "repo": self.gh_repo.strip() or derive_repo(self.github_url),
                "token": self.gh_token.strip(),
                "folder": LOGO_UPLOAD_FOLDER,
            },
        }

        self._busy = True
        self.gen_btn.disabled = True
        self.set_status("Working...", MUTED)
        threading.Thread(target=self._worker, args=(job,), daemon=True).start()

    def store_menu(self):
        self.store["projects"]["_menu"] = {
            "menu": copy.deepcopy(self.menu),
            "logo_url": self.page_logo_url,
            "item_id": self.item_ids[MODE_MENU],
        }
        self.save_store()

    @staticmethod
    def _single_content(job, logo_style, wants_logo):
        """Single-link mode -> (content, route, platform key, whether the center logo is used)."""
        if not job["raw"]:
            raise ValueError("Enter a link or username.")
        link = build_link(job["platform"], job["raw"])
        if not link.lower().startswith(("http",) + CONTACT_SCHEMES):
            link = "https://" + link
        key = job["platform"]
        has_logo = wants_logo and os.path.isfile(logo_path(key, logo_number(logo_style)))
        content, route = pick_single(link, job["link_type"], has_logo)
        return content, route, key, has_logo

    @staticmethod
    def _page_content(job):
        """All-in-one, data inside the link -> (short link to the links page, length of the long link).
        Everything personal travels in the '#' part; only the look is uploaded as designs/<id>.json."""
        if not job["items"]:
            raise ValueError("Add at least one link.")

        logo_id = None
        if job["page_logo"]:
            logo_id, logo_bytes = prepare_logo(job["page_logo"])
            github_upload_logo(job["gh"], logo_id, logo_bytes)

        design_id = None
        if job["design_name"]:
            design_id = slugify_design_name(job["design_name"])
            overwrite = True
        elif not design_is_default(job["design"]):
            design_id = design_id_for(job["design"])
            overwrite = False
        if design_id:
            github_put_file(
                job["gh"],
                f"{DESIGN_FOLDER}/{design_id}.json",
                design_json(job["design"]),
                f"Design {design_id}",
                overwrite=overwrite,
                what="the design",
            )

        payload = build_payload(job["name"], job["texts"], job["items"], logo_id, design_id)
        long_url = job["base_github"] + "#" + encode_payload(payload)
        return shorten_url(long_url), len(long_url)

    @staticmethod
    def _upload_visuals(job, design):
        """Uploads the logo and the background picture to the pictures repository.
        Returns (logo address, design with the picture address, picture address or None)."""
        _pages, assets, _templates = job["cfgs"]
        logo_url = job["page_logo_url"] or ""
        if job["page_logo"]:
            logo_id, data = prepare_logo(job["page_logo"])
            logo_url = upload_asset(assets, f"{logo_id}.png", data, "the logo")
        bg_url = None
        if job["bg_local"]:
            bg_id, data, ext = prepare_image(job["bg_local"], BG_UPLOAD_PX, "JPEG")
            bg_url = upload_asset(assets, f"{bg_id}.{ext}", data, "the background picture")
            design = copy.deepcopy(design)
            design["bg"]["bi"] = bg_url
        return logo_url, design, bg_url

    @staticmethod
    def _publish_card(job):
        """Card stored on GitHub -> (fixed link, info)."""
        pages = job["cfgs"][0]
        logo_url, design, bg_url = QRGeneratorApp._upload_visuals(job, job["design"])
        payload = build_payload(
            job["name"], job["texts"], job["items"], logo_url=logo_url or None, design=design, item_type="card"
        )
        display = job["name"] or job["texts"].get("name_en") or "Card"
        item_id = publish_item(pages, job["item_id"], payload, display)
        return page_link(job["base_github"], item_id), {"id": item_id, "logo_url": logo_url, "bg_url": bg_url}

    @staticmethod
    def _publish_menu(job):
        """Menu stored on GitHub -> (fixed link, info)."""
        pages, assets, _templates = job["cfgs"]
        menu = job["menu"]
        for section in menu["sections"]:
            for item in section["items"]:
                if item["img"] and os.path.isfile(item["img"]):
                    photo_id, data, ext = prepare_image(item["img"], DISH_UPLOAD_PX, "JPEG")
                    item["img_url"] = upload_asset(assets, f"{photo_id}.{ext}", data, "a menu photo")
                    item["img"] = ""
        logo_url, design, bg_url = QRGeneratorApp._upload_visuals(job, job["design"])
        payload = compile_menu(menu, design, logo_url)
        display = menu["name"] or menu["name_en"] or "Menu"
        item_id = publish_item(pages, job["item_id"], payload, display)
        return page_link(job["base_github"], item_id), {
            "id": item_id, "logo_url": logo_url, "bg_url": bg_url, "menu": menu,
        }  # fmt: skip

    @staticmethod
    def _save_files(folder, base, image, content, size_mm, max_version):
        png_path = os.path.join(folder, base + ".png")
        svg_path = os.path.join(folder, base + ".svg")
        image.convert("RGB").save(png_path, format="PNG")
        modules, module_mm = save_svg(content, svg_path, size_mm, max_version)
        return png_path, svg_path, modules, module_mm

    @staticmethod
    def _save_outputs(job, image, content, max_version=MAX_VERSION):
        """Writes the PNG and SVG. Returns (png path, svg path, modules, module mm, where-message)."""
        png_path, svg_path, modules, module_mm = QRGeneratorApp._save_files(
            job["folder"], job["filename"], image, content, job["size_mm"], max_version
        )

        in_private = os.path.abspath(job["folder"]).startswith(os.path.abspath(job["user_dir"]))
        exported = False
        if in_private:
            exported = export_to_shared(png_path)
            exported = export_to_shared(svg_path) and exported

        if exported:
            where = "Saved to shared storage (Pictures)."
        elif in_private and IS_ANDROID:
            where = f"Saved only in the app folder: {job['folder']}. Allow storage access and generate again."
        else:
            where = f"Saved in {job['folder']}"
        return png_path, svg_path, modules, module_mm, where

    @staticmethod
    def _save_batch(job, contents, max_version):
        """Serial batch: one PNG + SVG per code, in <file name>_batch. Returns a status sentence."""
        folder = os.path.join(job["folder"], job["filename"] + "_batch")
        os.makedirs(folder, exist_ok=True)
        in_private = os.path.abspath(folder).startswith(os.path.abspath(job["user_dir"]))
        for number, text in enumerate(contents, 1):
            base = f"{number:04d}_{_safe_filename(text)[:50]}"
            image = generate_qr(text, ALL_KEY, "Black & White", False, max_version)
            png_path, svg_path, _m, _mm = QRGeneratorApp._save_files(folder, base, image, text, job["size_mm"], max_version)
            if in_private:
                export_to_shared(png_path)
                export_to_shared(svg_path)
        return f"{len(contents)} codes saved in {folder}"

    def _worker(self, job):
        try:
            logo_style = "Color" if job["logo_choice"] == "Color logo" else "Black & White"
            wants_logo = job["logo_choice"] != "No logo"
            mode = job["mode"]
            extra, long_length, max_version, contents = {}, 0, MAX_VERSION, None

            if mode == MODE_SINGLE:
                content, route, key, has_logo = self._single_content(job, logo_style, wants_logo)
            elif mode == MODE_ALL:
                if job["store"] == STORE_GITHUB:
                    content, extra = self._publish_card(job)
                    route = "item"
                else:
                    content, long_length = self._page_content(job)
                    route = "page"
                key, has_logo = ALL_KEY, False
            elif mode == MODE_MENU:
                content, extra = self._publish_menu(job)
                route, key, has_logo = "item", ALL_KEY, False
            else:
                contents = job["contents"]
                content = contents[0]
                route, key, has_logo, max_version = "offline", ALL_KEY, False, OFFLINE_MAX_VERSION

            image = generate_qr(content, key, logo_style, has_logo, max_version)
            png_path, svg_path, modules, module_mm, where = self._save_outputs(job, image, content, max_version)

            message = f"{ROUTE_TEXT[route]}\n{job['filename']}.png + .svg\n{where}"
            if contents and len(contents) > 1:
                message += "\n" + self._save_batch(job, contents, max_version)
            if extra.get("id"):
                message += "\nSaved on GitHub. It can take about a minute before the page shows the change."
            if route == "page" and long_length > 1800:
                message += f"\nThe page data is long ({long_length} characters)."
            if module_mm < MIN_MODULE_MM:
                message += (
                    f"\nSquares are only {module_mm:.2f} mm: make the code at least "
                    f"{math.ceil(MIN_MODULE_MM * modules)} mm wide so it scans reliably."
                )

            result = {
                "mode": mode,
                "png": png_path,
                "svg": svg_path,
                "content": content,
                "folder": job["folder"],
                "modules": modules,
                "module_mm": module_mm,
                "extra": extra,
                "message": message,
            }
            Clock.schedule_once(lambda _dt: self._on_success(result))
        except Exception as e:
            error = str(e)
            Clock.schedule_once(lambda _dt: self._on_error(error))

    def _on_success(self, r):
        self._busy = False
        self.gen_btn.disabled = False
        self._last_png, self._last_svg = r["png"], r["svg"]
        self._last_content, self._last_folder = r["content"], r["folder"]
        self.preview.source = r["png"]
        self.preview.reload()
        self.preview_hint.opacity = 0
        self.stat_modules.set(f"{r['modules']}x{r['modules']}")
        self.stat_size.set(f"{r['module_mm']:.2f} mm")
        self.stat_margin.set(f"{BORDER_MODULES * r['module_mm']:.1f} mm")
        self.content_label.text = r["content"]

        extra = r["extra"]
        if extra.get("id"):
            self.item_ids[r["mode"]] = extra["id"]
        if extra.get("logo_url"):
            self.page_logo_url, self.page_logo = extra["logo_url"], None
            self._show_logo_state()
        if extra.get("bg_url"):
            self.design["bg"]["bi"], self.bg_local = extra["bg_url"], None
        if extra.get("menu"):
            self._merge_menu_photos(extra["menu"])
        if r["mode"] in (MODE_ALL, MODE_MENU):
            self._refresh_page_bars()
            if r["mode"] == MODE_MENU:
                self.store_menu()
            else:
                self.store_project("_last")
        self.set_status(r["message"], SUCCESS)

    def _merge_menu_photos(self, uploaded):
        """Photos uploaded in the background: keep their addresses so they are not uploaded again."""
        mine = self.menu["sections"]
        if len(mine) != len(uploaded["sections"]):
            return
        changed = False
        for section, done in zip(mine, uploaded["sections"]):
            if len(section["items"]) != len(done["items"]):
                continue
            for item, finished in zip(section["items"], done["items"]):
                if finished["img_url"] != item["img_url"] and not finished["img"]:
                    item["img_url"], item["img"] = finished["img_url"], ""
                    changed = True
        if changed:
            self._render_menu()

    def _on_error(self, error):
        self._busy = False
        self.gen_btn.disabled = False
        self.set_status(error, ERROR)


if __name__ == "__main__":
    QRGeneratorApp().run()
