# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Smeta 3D"
# description = "Смета 3D-печати: цена и себестоимость каждой нарезки и каждой модели, прямо в панели рядом с 3D-видом. Читает только G-code предпросмотра Orca."
# author = "artemalv"
# version = "1.5.0"
# ///
"""Смета 3D-печати — плагин для OrcaSlicer 2.5+.

После каждой нарезки плагин читает временный G-code, который Orca пишет для предпросмотра
(папка orcaslicer_model во временной папке системы), берёт из него вес, время, пластик и
принтер и показывает смету в панели. Ставки берутся с сайта «Смета 3D» (тот же файл rates.dat, что у калькулятора; читает страница
панели, у самого плагина сети нет). Без сайта ставки принтера и цена пластика запоминаются
отдельно для каждого профиля Orca.

  Orca --SlicingJobComplete--> plugin.refresh() --panel.post(state)--> страница
  страница --postMessage({command:'save', settings})--> plugin (конфиг возможности в Orca)
"""
import glob
import json
import math
import os
import re
import time

import orca

PLUGIN_TITLE = "Смета 3D-печати"
SETTINGS_FILE = "settings.json"

DEFAULT_SETTINGS = {
    "auto_open": True,
    "useSite": True,    # ставки, принтеры и цены пластика — с сайта «Смета 3D» (читает страница панели)
    "site": None,       # последние ставки с сайта: работают и без интернета
    "printers": {},     # имя профиля принтера Orca -> ставки
    "filaments": {},    # имя профиля пластика Orca -> {"price": ₽/кг, "from_orca": bool}
    "printer_default": {"price": 75000, "life": 6000, "maint": 12, "power": 130, "extraMin": 0},
    "filament_default": {"price": 1500, "from_orca": False},
    "money": {"rate": 600, "setupMin": 15, "plateMin": 5, "postMin": 3, "kwh": 7.5, "risk": 5, "waste": 5,
              "markup": 100, "adjust": 0, "minOrder": 500, "taxRev": 6, "vat": 0,
              "inserts": 0, "insertPrice": 12, "paint": 0, "cadH": 0, "cadRate": 1500, "packaging": 0,
              "twoRate": False, "kwhNight": 3.5, "nightFrom": 23, "nightTo": 7, "rushPct": 30,
              "presets": [{"n": "Розница", "v": 100}, {"n": "Опт", "v": 50}, {"n": "Свои", "v": 30}]},
    "order": {"qty": 1, "partsOverride": 0, "name": "", "kit": False, "need": {}, "deadline": "", "start": ""},
    "ui": {"open": ["models", "order", "filaments"], "modelsSeen": True},
}


# ---------------------------------------------------------------- G-code

def _dur(s):
    total = 0.0
    for num, unit in re.findall(r"(\d+(?:\.\d+)?)\s*([dhms])", s or "", re.I):
        total += float(num) * {"d": 86400, "h": 3600, "m": 60, "s": 1}[unit.lower()]
    return total


def _nums(s):
    return [float(x) for x in re.findall(r"-?\d+(?:\.\d+)?", s or "")]


def _read_ends(path, limit=512 * 1024):
    size = os.path.getsize(path)
    with open(path, "rb") as f:
        head = f.read(min(size, limit))
        tail = b""
        if size > limit:
            f.seek(max(limit, size - limit))
            tail = f.read()
    return head.decode("utf-8", "replace") + "\n" + tail.decode("utf-8", "replace")


_OBJ_START = re.compile(r"^; printing object (.+?)(?: id:(\d+) copy (\d+))?\s*$")
_OBJ_STOP = re.compile(r"^; stop printing object (.+?)(?: id:(\d+) copy (\d+))?\s*$")
_KL = re.compile(r"^EXCLUDE_OBJECT_(START|END) NAME=(\S+)")
_KLN = re.compile(r"^(.*)_id_(\d+)_copy_(\d+)$")
_M486 = re.compile(r"^M486 S(-?\d+)(?: A\"?([^\"\n]*)\"?)?")

def parse_objects(path):
    """По каждой модели на столе: длина выдавленной нити по экструдерам и оценка времени движений.
    Отрезки вне меток объектов (башня, продувка, юбка, парковка) копятся в общий котёл."""
    objs = {}          # key -> {"name","id","copies":set,"e":{tool:mm},"t":sec}
    shared_e, shared_t = {}, 0.0
    cur = None; cur_id = None; box = None; tool = 0; rel_e = True; rel_xyz = False
    x = y = z = 0.0; e_abs = 0.0; f = 3000.0
    m486_names = {}
    hypot = math.hypot
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            c = line[0] if line else ""
            if c == "G":
                c1 = line[1:3]
                if c1 in ("1 ", "0 ", "2 ", "3 "):
                    sc = line.find(";")
                    toks = (line[:sc] if sc >= 0 else line).split()
                    nx, ny, de = x, y, 0.0
                    for t in toks[1:]:
                        k = t[0]
                        try:
                            v = float(t[1:])
                        except ValueError:
                            continue
                        if k == "X": nx = x + v if rel_xyz else v
                        elif k == "Y": ny = y + v if rel_xyz else v
                        elif k == "Z": z = z + v if rel_xyz else v
                        elif k == "E":
                            if rel_e: de = v
                            else: de = v - e_abs; e_abs = v
                        elif k == "F" and v > 0: f = v
                    d = hypot(nx - x, ny - y)
                    x, y = nx, ny
                    dt = (d if d > 0 else abs(de)) / f * 60.0
                    ext = de > 0 and d > 0          # подача без движения — это возврат после ретракта, не пластик
                    if cur is None:
                        shared_t += dt
                        if ext: shared_e[tool] = shared_e.get(tool, 0.0) + de
                    else:
                        cur["t"] += dt
                        if ext:
                            cur["e"][tool] = cur["e"].get(tool, 0.0) + de
                            if box is not None:   # где модель лежит на столе — для карты стола в панели
                                if nx < box[0]: box[0] = nx
                                elif nx > box[2]: box[2] = nx
                                if ny < box[1]: box[1] = ny
                                elif ny > box[3]: box[3] = ny
                elif line.startswith("G92"):
                    for t in line.split(";")[0].split()[1:]:
                        if t[0] == "E":
                            try: e_abs = float(t[1:])
                            except ValueError: pass
                elif line.startswith("G90"): rel_xyz = False
                elif line.startswith("G91"): rel_xyz = True
                continue
            if c == "T":
                try:
                    n = int(line[1:].split()[0])
                    if 0 <= n < 64: tool = n
                except (ValueError, IndexError):
                    pass
                continue
            if c == "M":
                if line.startswith("M83"): rel_e = True
                elif line.startswith("M82"): rel_e = False
                elif line.startswith("M620 S") and "A" in line[6:10]:
                    try:
                        n = int(line[6:].split("A")[0])
                        if 0 <= n < 64: tool = n
                    except ValueError: pass
                elif line.startswith("M486"):
                    m = _M486.match(line)
                    if m:
                        n = int(m.group(1))
                        if m.group(2) is not None: m486_names[n] = m.group(2)
                        elif n < 0: cur = cur_id = None
                        else:
                            nm = m486_names.get(n, "Модель %d" % (n + 1)); cur, cur_id = _obj(objs, nm, str(n), "0"), _okey(nm, str(n), "0"); box = cur["boxes"].setdefault("0", [1e9, 1e9, -1e9, -1e9])
                continue
            if c == ";":
                if line.startswith("; printing object"):
                    m = _OBJ_START.match(line)
                    if m:
                        nm, oid, cp = m.group(1), m.group(2) or m.group(1), m.group(3) or "0"
                        cur, cur_id = _obj(objs, nm, oid, cp), _okey(nm, oid, cp); box = cur["boxes"].setdefault(str(cp), [1e9, 1e9, -1e9, -1e9])
                elif line.startswith("; stop printing object"):
                    m = _OBJ_STOP.match(line)
                    if not m or _okey(m.group(1), m.group(2) or m.group(1), m.group(3) or "0") == cur_id:
                        cur = cur_id = None
                elif line.startswith("; MANUAL_TOOL_CHANGE T"):
                    try: tool = int(line[22:].split()[0])
                    except (ValueError, IndexError): pass
                continue
            if c == "E" and line.startswith("EXCLUDE_OBJECT_"):
                m = _KL.match(line)
                if m:
                    # Orca пишет и «; printing object», и EXCLUDE_OBJECT (имя с заменой символов, а END —
                    # уже после «printing object» следующей модели), поэтому модели сверяются по ключу
                    n = _KLN.match(m.group(2))
                    nm, oid, cp = (n.group(1), n.group(2), n.group(3)) if n else (m.group(2), m.group(2), "0")
                    k = _okey(nm, oid, cp)
                    if m.group(1) == "END":
                        if k == cur_id: cur = cur_id = None
                    elif k != cur_id:
                        cur, cur_id = _obj(objs, nm, oid, cp), k; box = cur["boxes"].setdefault(str(cp), [1e9, 1e9, -1e9, -1e9])
    out = []
    for o in objs.values():
        boxes = [[round(v, 1) for v in b] for b in o["boxes"].values() if b[2] > b[0]]
        out.append({"name": o["name"], "copies": len(o["copies"]), "e": {str(k): v for k, v in o["e"].items()}, "t": o["t"], "boxes": boxes})
    return {"objects": out, "sharedE": {str(k): v for k, v in shared_e.items()}, "sharedT": shared_t}

def _norm(name):
    return re.sub(r"[^0-9a-zA-Zа-яА-ЯёЁ]", "", name or "").lower()


def _okey(name, oid, copy):
    return (_norm(name), str(oid), str(copy))


def _obj(objs, name, oid, copy):
    key = (_norm(name), str(oid))
    o = objs.get(key)
    if o is None:
        o = objs[key] = {"name": name, "copies": set(), "e": {}, "t": 0.0, "boxes": {}}
    elif "[" in name and "[" not in o["name"]:
        o["name"] = name   # исходное имя из комментария лучше имени для Klipper
    o["copies"].add(copy)
    return o


def split_by_objects(path, fil, mm, machine_s):
    """Вес и время каждой модели на столе. Длина нити по каждой модели переводится в граммы тем же
    соотношением г/мм, что у Orca, а общий расход (башня, продувка, юбка) делится между моделями
    пропорционально их собственному пластику. Время станка делится по оценке времени движений."""
    raw = parse_objects(path)
    objs = raw["objects"]
    if not objs:
        return None
    # одинаковые модели (одно имя и почти одинаковый расход) — одна строка с несколькими копиями
    rows = []
    for o in objs:
        e = sum(o["e"].values()) / max(1, o["copies"])
        for r in rows:
            if r["name"] == o["name"] and abs(r["_e"] - e) <= 0.02 * max(e, r["_e"], 1e-9):
                r["copies"] += o["copies"]; r["t"] += o["t"]; r["boxes"] += o.get("boxes", [])
                for k, v in o["e"].items():
                    r["e"][k] = r["e"].get(k, 0.0) + v
                break
        else:
            rows.append({"name": o["name"], "copies": o["copies"], "t": o["t"], "e": dict(o["e"]), "_e": e, "boxes": list(o.get("boxes", []))})
    own, total_own = [], {}
    for r in rows:
        g = {}
        for f in fil:
            slot = f["slot"]; e = r["e"].get(str(slot - 1), 0.0)
            ratio = f["grams"] / mm[slot - 1] if slot - 1 < len(mm) and mm[slot - 1] > 0 else 0.0
            if not ratio and f.get("density"):
                ratio = math.pi * 1.75 ** 2 / 4 * f["density"] / 1000
            g[slot] = e * ratio
            total_own[slot] = total_own.get(slot, 0.0) + g[slot]
        own.append(g)
    all_own = sum(total_own.values()) or 1.0
    t_sum = sum(r["t"] for r in rows) or 1.0
    out, overhead = [], 0.0
    for r, g in zip(rows, own):
        by_slot, own_g = [], sum(g.values())
        for f in fil:
            slot = f["slot"]; extra = max(0.0, f["grams"] - total_own.get(slot, 0.0))
            w = g[slot] / total_own[slot] if total_own.get(slot) else own_g / all_own
            by_slot.append(round(g[slot] + extra * w, 4))
        out.append({"name": re.sub(r"\.(stl|3mf|step|stp|obj|amf)$", "", r["name"], flags=re.I), "copies": r["copies"],
                    "ownG": round(own_g, 3), "gramsBySlot": by_slot, "grams": round(sum(by_slot), 3),
                    "timeS": round((machine_s or 0) * r["t"] / t_sum, 1), "boxes": r["boxes"]})
    overhead = sum(f["grams"] for f in fil) - sum(total_own.values())
    return {"objects": out, "overheadG": round(max(0.0, overhead), 3)}


def _bed(area):
    pts = re.findall(r"(-?[\d.]+)x(-?[\d.]+)", area or "")
    if len(pts) < 3:
        return None
    xs = [float(a) for a, _ in pts]; ys = [float(b) for _, b in pts]
    return [min(xs), min(ys), max(xs), max(ys)]


def parse_gcode(path):
    """Вес, стоимость и время из G-code Orca. Вес и стоимость — по каждому пластику (по номеру экструдера/слота),
    как Orca пишет их в конце файла: «; filament used [g] = a, b» и «; filament cost = a, b»."""
    text = _read_ends(path)

    def grab(pattern):
        m = re.search(pattern, text, re.I | re.M)
        return m.group(1).strip() if m else None

    def cfg(key):
        m = re.search(r"^; " + re.escape(key) + r" = (.*)$", text, re.M)
        return m.group(1).strip() if m else None

    def cfg_list(key):
        v = cfg(key)
        return [x.strip().strip('"') for x in v.split(";")] if v else []

    grams = _nums(grab(r"^; filament used \[g\]\s*=\s*([\d.,\s]+?)$")) or _nums(grab(r"total filament weight \[g\]\s*[:=]\s*([\d.,\s]+?)$"))
    costs = _nums(grab(r"^; filament cost\s*=\s*([\d.,\s]+?)$"))
    names = cfg_list("filament_settings_id")
    prices = _nums(cfg("filament_cost"))
    dens = _nums(cfg("filament_density"))
    types = [x.strip().strip('"') for x in re.split(r"[;,]", cfg("filament_type") or "") if x.strip()]
    fil = []
    for i, g in enumerate(grams):
        if g <= 0:
            continue
        fil.append({"slot": i + 1, "name": names[i] if i < len(names) else "Пластик %d" % (i + 1),
                    "grams": g, "orcaCost": costs[i] if i < len(costs) else None,
                    "orcaPrice": prices[i] if i < len(prices) else None, "density": dens[i] if i < len(dens) else None,
                    "type": types[i] if i < len(types) else ""})
    t_model = grab(r"model printing time:\s*([^;\n]+)")
    t_total = grab(r"total estimated time:\s*([^;\n]+)") or grab(r"estimated printing time \(normal mode\)\s*=\s*([^\n]+)")
    total_g = sum(f["grams"] for f in fil)
    machine_s = _dur(t_total) if t_total else (_dur(t_model) if t_model else None)
    # подогрев камеры: включён у какого-нибудь из использованных пластиков
    act = _nums(cfg("activate_chamber_temp_control"))
    ch_t = _nums(cfg("chamber_temperature") or cfg("chamber_temperatures"))
    chamber_c = 0.0
    for f in fil:
        i = f["slot"] - 1
        if i < len(ch_t) and (not act or (i < len(act) and act[i] > 0)):
            chamber_c = max(chamber_c, ch_t[i])
    bed_c = _nums(cfg("first_layer_bed_temperature"))
    mm = _nums(grab(r"^; filament used \[mm\]\s*=\s*([\d.,\s]+?)$"))
    try:
        split = split_by_objects(path, fil, mm, machine_s) if fil else None
    except Exception:
        split = None
    orca_cost = grab(r"^; total filament cost\s*=\s*([\d.]+)")
    return {
        "path": path,
        "mtime": os.path.getmtime(path),
        "grams": round(total_g, 3) if fil else None,
        "filaments": fil,
        "orcaCost": float(orca_cost) if orca_cost else (round(sum(f["orcaCost"] or 0 for f in fil), 2) if any(f["orcaCost"] for f in fil) else None),
        # время станка: у Orca общее время уже включает подготовку (нагрев, калибровку)
        "machineS": machine_s,
        "chamberC": chamber_c,
        "bed": _bed(cfg("printable_area")),
        "bedC": bed_c[0] if bed_c else None,
        "model": (cfg("printer_model") or "").strip('"'),
        "objects": split["objects"] if split else [],
        "overheadG": split["overheadG"] if split else 0,
        "modelS": _dur(t_model) if t_model else None,
        "layers": int(grab(r"total layer number:\s*(\d+)") or grab(r"total layers count\s*=\s*(\d+)") or 0) or None,
        "changes": int(grab(r"total filament change\s*=\s*(\d+)") or 0),
        "printer": (cfg("printer_settings_id") or "").strip('"'),
        "process": (cfg("print_settings_id") or "").strip('"'),
        "layer": cfg("layer_height"),
        "walls": cfg("wall_loops"),
        "infill": cfg("sparse_infill_density"),
    }


def temp_roots():
    """Временные папки системы. tempfile.gettempdir() не используем: он пробует создать и удалить
    файл в TEMP, а Orca спрашивает разрешение на каждую такую операцию."""
    roots, seen = [], set()
    cands = [os.environ.get("TEMP"), os.environ.get("TMP"), os.environ.get("TMPDIR")]
    if os.environ.get("LOCALAPPDATA"):
        cands.append(os.path.join(os.environ["LOCALAPPDATA"], "Temp"))
    cands += ["/tmp", "/var/tmp"]
    for r in cands:
        if not r:
            continue
        k = os.path.normcase(os.path.abspath(r))
        if k not in seen and os.path.isdir(r):
            seen.add(k)
            roots.append(r)
    return roots


def model_dirs():
    """Папки, куда Orca пишет G-code предпросмотра. Плагин читает только их."""
    return [os.path.join(r, "orcaslicer_model") for r in temp_roots()]


def _gcode_complete(path):
    """Orca дописывает итоги (вес, время) в конец файла — без них файл ещё пишется."""
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as f:
            f.seek(max(0, size - 64 * 1024))
            tail = f.read()
        return b"filament used [g]" in tail or b"total filament weight" in tail
    except OSError:
        return False


def find_temp_gcode(newer_than=0.0):
    """Свежий G-code предпросмотра: .../orcaslicer_model/<дата>/<время>#<pid>#<id>/Metadata/.<pid>.<n>.gcode.
    Папку проекта Orca может унаследовать от прошлого запуска (в имени папки — чужой pid), а имя файла
    всегда содержит pid текущего процесса. Поэтому ищем файл по своему pid в любой папке, а если такого
    нет — самый новый G-code, записанный после начала нарезки."""
    pid = os.getpid()
    own, own_t, any_, any_t = None, newer_than, None, newer_than
    for model_dir in model_dirs():
        if not os.path.isdir(model_dir):
            continue
        for path in glob.glob(os.path.join(glob.escape(model_dir), "*", "*", "Metadata", ".*.gcode")):
            try:
                t = os.path.getmtime(path)
            except OSError:
                continue
            if os.path.basename(path).startswith(".%d." % pid):
                if t > own_t:
                    own, own_t = path, t
            elif t > any_t:
                any_, any_t = path, t
    if own:
        return own
    return any_ if newer_than > 0 else None


def model_parts():
    """Сколько деталей (копий) на столе."""
    try:
        model = orca.host.model()
        n = 0
        for obj in model.objects():
            n += max(1, int(obj.instance_count()))
        return n or 1
    except Exception:
        return 1


# ---------------------------------------------------------------- настройки

def _merge(saved):
    s = json.loads(json.dumps(DEFAULT_SETTINGS))
    for k, v in (saved or {}).items():
        if isinstance(v, dict) and isinstance(s.get(k), dict):
            s[k].update(v)
        else:
            s[k] = v
    return s


def load_settings(cap=None):
    """Настройки хранятся в конфиге возможности (get_config/save_config Orca 2.5): переживают
    обновление плагина и видны во вкладке «Настройки» окна «Плагины». Файл — запасной вариант."""
    if cap is not None:
        try:
            saved = json.loads(cap.get_config() or "{}")
            if isinstance(saved, dict) and saved:
                return _merge(saved)
        except Exception as e:
            print("Smeta 3D: конфиг Orca не прочитался:", e)
    return _merge({})


def save_settings(s, cap=None):
    """True — сохранено. Сначала в конфиг Orca, при неудаче — в файл рядом с плагином."""
    if cap is not None:
        try:
            if cap.save_config(json.dumps(s, ensure_ascii=False)) is not False:
                return True
        except Exception as e:
            print("Smeta 3D: конфиг Orca не записался:", e)
    return False


# ---------------------------------------------------------------- панель

PAGE = r"""
<style>
  :root{
    --bg:var(--orca-bg,#1e2226); --fg:var(--orca-fg,#e6e9ec); --accent:var(--orca-accent,#009688); --line:var(--orca-border,#3a4046);
    --muted:var(--orca-muted,#9aa3ab); --soft:rgba(127,127,127,.12); --ok:#3fb27f; --warn:#e0a63b; --bad:#e2566e;
    --c-cost:#5b8fd6; --c-profit:#3fb27f; --c-tax:#e0a63b;
    --mono:ui-monospace,"Cascadia Mono",Consolas,"JetBrains Mono",monospace;
  }
  *{box-sizing:border-box}
  body{margin:0;padding:0 0 16px;background:var(--bg);color:var(--fg);font:13px/1.4 system-ui,"Segoe UI",sans-serif}
  .mono{font-family:var(--mono);font-variant-numeric:tabular-nums}
  .muted{color:var(--muted)}
  /* статус */
  .status{display:flex;align-items:center;gap:8px;padding:8px 12px;border-bottom:1px solid var(--line);font-size:12.5px}
  .status .dot{width:8px;height:8px;border-radius:50%;background:var(--muted);flex:none}
  .status.fresh .dot{background:var(--ok)} .status.stale .dot{background:var(--warn)} .status.slicing .dot{background:var(--accent);animation:pulse 1s infinite alternate}
  .status.stale{background:rgba(224,166,59,.10)}
  .status .txt{flex:1;min-width:0}
  .status .txt b{font-weight:600}
  .status .sub{display:block;color:var(--muted);font-size:11.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
  @keyframes pulse{to{opacity:.3}}
  .icon{border:1px solid var(--line);background:transparent;color:var(--fg);border-radius:6px;width:28px;height:26px;cursor:pointer;flex:none;font-size:14px;line-height:1}
  .icon:hover,.b:hover{border-color:var(--accent)}
  /* главный блок */
  .hero{padding:12px 12px 10px;transition:opacity .2s}
  .hero.dim,#modelList.dim{opacity:.55}
  .hero .lbl{font-size:11.5px;color:var(--muted)}
  .hero .big{font:700 30px/1.1 system-ui,"Segoe UI",sans-serif;font-variant-numeric:tabular-nums;letter-spacing:-.01em;margin:2px 0}
  .hero .sum{font:12px var(--mono);color:var(--muted)}
  .bar{display:flex;height:8px;border-radius:4px;overflow:hidden;background:var(--soft);margin:10px 0 6px;gap:2px}
  .bar span{display:block;height:100%}
  .legend{display:flex;flex-wrap:wrap;gap:4px 12px;font-size:11.5px;color:var(--muted)}
  .legend i{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:5px;vertical-align:0}
  .legend b{color:var(--fg);font-family:var(--mono);font-weight:600}
  [hidden]{display:none!important}
  .actions{display:flex;gap:6px;align-items:center;margin-top:10px}
  .empty{padding:14px 12px;display:flex;flex-direction:column;gap:6px;font-size:12.5px}
  .empty ol{margin:0;padding-left:18px;color:var(--muted)}
  .err{margin:0 12px 8px;padding:6px 8px;border-radius:6px;background:rgba(226,86,110,.12);color:var(--bad);font-size:12px}
  /* разделы */
  details{border-top:1px solid var(--line)}
  details>summary{cursor:pointer;list-style:none;display:flex;align-items:center;gap:8px;padding:9px 12px;font-weight:600;font-size:12.5px}
  details>summary::-webkit-details-marker{display:none}
  details>summary::before{content:"▸";color:var(--muted);font-size:11px;width:10px}
  details[open]>summary::before{content:"▾"}
  details>summary small{margin-left:auto;font:500 12px var(--mono);color:var(--muted)}
  details .body{padding:0 12px 12px;display:flex;flex-direction:column;gap:10px}
  .grid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:10px 8px}
  .grid>*{min-width:0}
  label.f{display:flex;flex-direction:column;gap:3px;min-width:0}
  label.f>span,.f>.lab{font-size:11.5px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
  .inp{display:flex;align-items:center;border:1px solid var(--line);border-radius:6px;height:28px;background:rgba(0,0,0,.08)}
  .inp:focus-within{border-color:var(--accent)}
  .inp input{flex:1;min-width:0;width:100%;border:0;background:transparent;color:var(--fg);padding:0 7px;font:13px var(--mono);outline:none}
  .inp input:disabled{opacity:.6}
  .inp input[type=datetime-local]{font-size:11.5px;padding:0 4px;min-width:0}
  .inp input[type=datetime-local]::-webkit-calendar-picker-indicator{margin:0;padding:0;opacity:.6}
  .inp em{font-style:normal;font:11px var(--mono);color:var(--muted);padding-right:7px;white-space:nowrap}
  .quick{display:flex;gap:3px;flex-wrap:wrap}
  .quick button{border:1px solid var(--line);background:transparent;color:var(--muted);border-radius:4px;padding:0 6px;font:11px/18px var(--mono);cursor:pointer}
  .quick button:hover,.quick button.on{border-color:var(--accent);color:var(--fg)}
  .chk{display:flex;align-items:center;gap:6px;font-size:12px;color:var(--muted);cursor:pointer}
  .hint{font-size:11.5px;color:var(--muted);margin:0;overflow-wrap:anywhere}
  /* пластики */
  .fil{border:1px solid var(--line);border-radius:8px;padding:8px;display:flex;flex-direction:column;gap:6px}
  .fil .hd{display:flex;justify-content:space-between;gap:8px;align-items:baseline}
  .fil .nm{font-weight:600;font-size:12.5px;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .fil .g{font:12px var(--mono);color:var(--muted);white-space:nowrap}
  .fil .row2{display:grid;grid-template-columns:1fr auto;gap:8px;align-items:center}
  .fil .sum2{font:600 12.5px var(--mono);white-space:nowrap}
  .cmp{font-size:11.5px;color:var(--muted);display:flex;justify-content:space-between;gap:8px}
  .cmp b{color:var(--fg);font-family:var(--mono);font-weight:600}
  /* строки сметы */
  .row{display:flex;align-items:center;gap:8px;font-size:12.5px;padding:3px 0}
  .row .l{flex:1;min-width:0}
  .row .pc{font:11px var(--mono);color:var(--muted);width:36px;text-align:right}
  .row .r{font-family:var(--mono);white-space:nowrap;min-width:72px;text-align:right}
  .row i{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:6px}
  .row.b{font-weight:700;border-top:1px solid var(--line);padding-top:6px;margin-top:3px}
  .row.neg .r{color:var(--bad)} .row.pos .r{color:var(--ok)}
  .tiers{display:grid;grid-template-columns:repeat(3,1fr);gap:4px}
  .tier{border:1px solid var(--line);border-radius:6px;padding:4px;text-align:center;cursor:pointer;background:transparent;color:var(--fg)}
  .tier.on{border-color:var(--accent);background:rgba(0,150,136,.10)}
  .tier .q{font:10.5px var(--mono);color:var(--muted)} .tier .p{font:700 12.5px var(--mono)} .tier .d{font:10.5px var(--mono);color:var(--ok)}
  .b{border:1px solid var(--line);background:transparent;color:var(--fg);border-radius:6px;padding:4px 10px;font-size:12px;cursor:pointer}
  .b.pri{background:var(--accent);border-color:var(--accent);color:#fff}
  /* модели */
  .mdl{display:flex;flex-direction:column;gap:2px;padding:6px 0;border-bottom:1px dashed var(--line)}
  .mdl:last-of-type{border-bottom:0}
  .mdl .hd{display:flex;align-items:baseline;gap:6px}
  .mdl .nm{font-weight:600;font-size:12.5px;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
  .mdl .cp{font:11.5px var(--mono);color:var(--muted);white-space:nowrap}
  .mdl .pr{font:700 13px var(--mono);white-space:nowrap}
  .mdl .sub{display:flex;justify-content:space-between;gap:8px;font:11.5px var(--mono);color:var(--muted)}
  .mdl .mb{height:3px;border-radius:2px;background:var(--soft);overflow:hidden;margin-top:3px}
  .mdl .mb span{display:block;height:100%;background:var(--accent)}
  .kitbar{display:flex;align-items:center;justify-content:space-between;gap:6px;flex-wrap:wrap;margin-bottom:4px}
  .need{width:58px;height:22px;flex:none}
  .need input{font-size:12px;padding:0 4px}
  .need em{padding-right:4px}
  .mhead{display:flex;justify-content:space-between;font-size:11px;color:var(--muted)}
  .when{font-size:12px;padding:6px 8px;border-radius:6px;background:var(--soft)}
  .when b{font-family:var(--mono)} .when.ok{color:var(--ok)} .when.rush{color:var(--warn)} .when.late{color:var(--bad)}
  .mkedit{display:grid;grid-template-columns:1fr 70px;gap:4px 6px}
  .quick button.pre{font-family:inherit}
  .map{width:100%;height:auto;border:1px solid var(--line);border-radius:6px;background:var(--soft);margin-bottom:4px}
  .map rect.m{stroke:rgba(0,0,0,.35);stroke-width:.6;cursor:pointer;vector-effect:non-scaling-stroke}
  .map rect.m.hl{stroke:var(--fg);stroke-width:2.2}
  .mdl{cursor:pointer;border-radius:4px} .mdl.hl{background:rgba(0,150,136,.14);outline:1px solid var(--accent)}
  .heat{display:flex;align-items:center;gap:6px;font-size:10.5px;color:var(--muted)} .heat i{flex:1;height:5px;border-radius:3px;background:linear-gradient(90deg,#2aa198,#e0a63b,#e2566e)}
  textarea{width:100%;min-height:150px;border:1px solid var(--line);border-radius:6px;background:rgba(0,0,0,.08);color:var(--fg);font:11.5px/1.45 var(--mono);padding:6px;resize:vertical}
  .site{display:flex;align-items:center;gap:6px;flex-wrap:wrap;font-size:11.5px;padding:6px 8px;border:1px solid var(--line);border-radius:6px;background:var(--soft);margin:0 0 8px}
  .site .st{color:var(--muted);flex:1;min-width:120px} .site .st.bad{color:var(--warn)}
  .site-note{font-size:11px;color:var(--muted)}
  input:disabled{opacity:.7;cursor:not-allowed}
</style>

<div class="status" id="status"><span class="dot"></span><span class="txt" id="statusTxt">Жду данные от Orca…</span><button type="button" class="icon" id="refresh" title="Перечитать последнюю нарезку">↻</button></div>
<div class="err" id="err" hidden></div>
<div id="emptyBox" class="empty" hidden>
  <b>Нарежьте модель в Orca</b>
  <ol><li>Положите модель на стол и выберите профили.</li><li>Нажмите «Нарезать».</li><li>Цена появится здесь и будет обновляться после каждой нарезки.</li></ol>
</div>
<div class="hero" id="hero" hidden>
  <div class="lbl">Цена для клиента</div>
  <div class="big" id="total">—</div>
  <div class="sum" id="summary"></div>
  <div class="bar" id="bar"></div>
  <div class="legend" id="legend"></div>
  <p class="hint" id="noteInfo"></p>
</div>

<div id="main" hidden>
<div class="site" id="siteBox"><label class="chk"><input type="checkbox" id="useSite"> Ставки с сайта «Смета 3D»</label><span class="st" id="siteSt"></span><button type="button" class="icon" id="siteRef" title="Обновить ставки с сайта">↻</button></div>
<details data-sec="models" id="secModels" hidden><summary>По моделям <small id="sModels"></small></summary><div class="body" style="gap:4px">
  <div class="mhead"><span>модель · вес и время на 1 шт</span><span>цена за 1 шт</span></div>
  <svg class="map" id="plateMap" role="img" aria-label="Карта стола: цвет — цена детали"></svg>
  <div class="heat" id="heatLeg"><span>дешевле</span><i></i><span>дороже</span></div>
  <div id="modelList"></div>
  <p class="hint" id="modelHint"></p>
</div></details>
<details data-sec="order"><summary>Заказ <small id="sOrder"></small></summary><div class="body">
  <div class="grid">
    <div class="f"><label class="lab" for="qty" id="qtyLab">Тираж, шт</label><span class="inp"><input id="qty" type="number" min="1" step="1" data-k="order.qty"><em id="qtyUnit">шт</em></span>
      <div class="quick" data-quick="order.qty"><button type="button" data-v="1">1</button><button type="button" data-v="10">10</button><button type="button" data-v="50">50</button><button type="button" data-v="100">100</button></div></div>
    <div class="f"><label class="lab" for="parts" id="partsLab" title="Сколько деталей печатается за один стол. Пусто — по числу копий на столе в Orca">Деталей на столе</label><span class="inp"><input id="parts" type="number" min="0" step="1" data-k="order.partsOverride" placeholder="авто"><em id="partsAuto">авто</em></span>
      <span class="hint" id="partsHint"></span></div>
    <div class="f"><label class="lab" for="mk">Наценка на себестоимость</label><span class="inp"><input id="mk" type="number" min="0" step="5" data-k="money.markup"><em>%</em></span>
      <div class="quick" id="mkPresets"></div></div>
    <div class="f"><label class="lab" for="post" title="Снятие поддержек, зачистка — минут на каждую деталь">Ручная работа на 1 шт</label><span class="inp"><input id="post" type="number" min="0" step="1" data-k="money.postMin"><em>мин</em></span>
      <div class="quick" data-quick="money.postMin"><button type="button" data-v="0">0</button><button type="button" data-v="3">3</button><button type="button" data-v="10">10</button><button type="button" data-v="30">30</button></div></div>
  </div>
</div></details>

<details data-sec="filaments"><summary>Пластик <small id="sFil"></small></summary><div class="body">
  <div id="filList" style="display:flex;flex-direction:column;gap:8px"></div>
  <label class="f"><span title="Обрезки, концы катушек, неудачные старты — то, чего нет в G-code">Запас на потери сверх расчёта Orca</span><span class="inp"><input type="number" min="0" max="50" step="1" data-k="money.waste"><em>%</em></span></label>
  <p class="hint" id="wasteHint"></p>
  <div class="cmp" id="filCmp"></div>
</div></details>

<details data-sec="cost"><summary>Себестоимость и прибыль <small id="sCost"></small></summary><div class="body" id="rows"></div></details>
<details data-sec="tiers"><summary id="tiersLab">Цена за штуку при тираже</summary><div class="body"><div class="tiers" id="tiers"></div></div></details>

<details data-sec="printer"><summary>Принтер <small id="sPr"></small></summary><div class="body">
  <div class="grid">
    <label class="f"><span>Стоимость принтера</span><span class="inp"><input type="number" min="0" step="1000" data-k="pr.price"><em>₽</em></span></label>
    <label class="f"><span>Срок окупаемости</span><span class="inp"><input type="number" min="1" step="500" data-k="pr.life"><em>ч</em></span></label>
    <label class="f"><span>Расходники, ремонт</span><span class="inp"><input type="number" min="0" step="1" data-k="pr.maint"><em>₽/ч</em></span></label>
    <label class="f"><span title="Средняя за печать, не паспортная">Средняя мощность</span><span class="inp"><input type="number" min="0" step="10" data-k="pr.power"><em>Вт</em></span></label>
    <label class="f"><span title="Время Orca уже включает нагрев и калибровку. Здесь — то, чего Orca не знает: смена листа, ожидание">Доп. время на стол</span><span class="inp"><input type="number" min="0" step="1" data-k="pr.extraMin"><em>мин</em></span></label>
    <label class="f" id="fChP"><span title="Средняя мощность нагревателя камеры за печать. Прибавляется, только если в профиле пластика включён подогрев камеры">Нагрев камеры</span><span class="inp"><input type="number" min="0" step="50" data-k="pr.chamberPower"><em>Вт</em></span></label>
    <label class="f" id="fChM"><span title="Прогрев камеры перед печатью — Orca его не считает">Прогрев камеры на стол</span><span class="inp"><input type="number" min="0" step="1" data-k="pr.chamberMin"><em>мин</em></span></label>
    <label class="f"><span id="kwhLab">Тариф на электричество</span><span class="inp"><input type="number" min="0" step="0.1" data-k="money.kwh"><em>₽/кВт·ч</em></span></label>
  </div>
  <label class="chk"><input type="checkbox" data-k="money.twoRate"> Двухтарифный счётчик (день / ночь)</label>
  <div class="grid" id="nightBox">
    <label class="f"><span>Ночной тариф</span><span class="inp"><input type="number" min="0" step="0.1" data-k="money.kwhNight"><em>₽/кВт·ч</em></span></label>
    <div class="grid" style="gap:8px"><label class="f"><span>Ночь с</span><span class="inp"><input type="number" min="0" max="23" step="1" data-k="money.nightFrom"><em>ч</em></span></label>
    <label class="f"><span>до</span><span class="inp"><input type="number" min="0" max="23" step="1" data-k="money.nightTo"><em>ч</em></span></label></div>
  </div>
  <p class="hint" id="prHint"></p>
  <p class="hint" id="prPreset"></p>
</div></details>

<details data-sec="work"><summary>Работа и услуги <small id="sWork"></small></summary><div class="body"><div class="grid">
  <label class="f"><span>Ставка оператора</span><span class="inp"><input type="number" min="0" step="50" data-k="money.rate"><em>₽/ч</em></span></label>
  <label class="f"><span>Приём заказа, нарезка</span><span class="inp"><input type="number" min="0" step="1" data-k="money.setupMin"><em>мин</em></span></label>
  <label class="f"><span>Снятие со стола</span><span class="inp"><input type="number" min="0" step="1" data-k="money.plateMin"><em>мин/стол</em></span></label>
  <label class="f"><span>Покраска на 1 шт</span><span class="inp"><input type="number" min="0" step="10" data-k="money.paint"><em>₽</em></span></label>
  <label class="f"><span>Втулки на 1 шт</span><span class="inp"><input type="number" min="0" step="1" data-k="money.inserts"><em>шт</em></span></label>
  <label class="f"><span>Цена втулки</span><span class="inp"><input type="number" min="0" step="1" data-k="money.insertPrice"><em>₽</em></span></label>
  <label class="f"><span>3D-моделирование</span><span class="inp"><input type="number" min="0" step="0.5" data-k="money.cadH"><em>ч</em></span></label>
  <label class="f"><span>Ставка моделирования</span><span class="inp"><input type="number" min="0" step="100" data-k="money.cadRate"><em>₽/ч</em></span></label>
  <label class="f"><span>Упаковка на заказ</span><span class="inp"><input type="number" min="0" step="10" data-k="money.packaging"><em>₽</em></span></label>
</div></div></details>

<details data-sec="tax"><summary>Налоги и скидки <small id="sTax"></small></summary><div class="body">
  <div class="f"><span class="lab">Кнопки наценки для типовых клиентов</span><div id="mkEdit" class="mkedit"></div></div>
  <div class="grid">
  <div class="f"><label class="lab" for="tx" title="Цена = сумма ÷ (1 − ставка), чтобы после налога осталась нужная сумма">Налог с выручки</label><span class="inp"><input id="tx" type="number" min="0" max="50" step="0.5" data-k="money.taxRev"><em>%</em></span>
    <div class="quick" data-quick="money.taxRev"><button type="button" data-v="0">нет</button><button type="button" data-v="4">НПД 4</button><button type="button" data-v="6">6</button></div></div>
  <div class="f"><label class="lab" for="vat">НДС сверху цены</label><span class="inp"><input id="vat" type="number" min="0" max="30" step="1" data-k="money.vat"><em>%</em></span>
    <div class="quick" data-quick="money.vat"><button type="button" data-v="0">0</button><button type="button" data-v="5">5</button><button type="button" data-v="22">22</button></div></div>
  <div class="f"><label class="lab" for="adj">Скидка (−) или срочность (+)</label><span class="inp"><input id="adj" type="number" min="-90" max="300" step="5" data-k="money.adjust"><em>%</em></span>
    <div class="quick" data-quick="money.adjust"><button type="button" data-v="-10">−10</button><button type="button" data-v="0">0</button><button type="button" data-v="50">+50</button></div></div>
  <label class="f"><span>Минимальная сумма заказа</span><span class="inp"><input type="number" min="0" step="50" data-k="money.minOrder"><em>₽</em></span></label>
  <label class="f"><span title="Доля деталей, которые придётся печатать заново">Резерв на брак</span><span class="inp"><input type="number" min="0" max="60" step="1" data-k="money.risk"><em>%</em></span></label>
</div></div></details>

</div>

<script>
(function(){
  var bridge = window.orca || { postMessage:function(){}, onMessage:function(){} };
  var S = null, slice = null, autoParts = 1, err = null, status = 'none', staleReason = '', lastKeys = '';
  var $ = function(id){ return document.getElementById(id); };
  function nf(v, d){ v = isFinite(v) ? v : 0; return v.toLocaleString('ru-RU', { minimumFractionDigits:d||0, maximumFractionDigits:d||0 }); }
  function rub(v){ return nf(v, Math.abs(v) < 100 ? 2 : 0) + ' ₽'; }
  function grams(v){ return v >= 1000 ? nf(v/1000, 2) + ' кг' : nf(v, v < 10 ? 2 : 1) + ' г'; }
  function dur(s){ s = Math.max(0, Math.round(s||0)); var d = Math.floor(s/86400), h = Math.floor(s%86400/3600), m = Math.round(s%3600/60); return d ? d + ' д ' + h + ' ч' : h ? h + ' ч ' + (m<10?'0':'') + m + ' мин' : m + ' мин'; }
  function esc(s){ var d = document.createElement('span'); d.textContent = s == null ? '' : String(s); return d.innerHTML; }
  function short(n){ return String(n || '').replace(/\s*@.*$/, ''); }
  function clone(o){ return JSON.parse(JSON.stringify(o)); }

  function fils(){ return (slice && slice.filaments) || []; }
  /* ---------- ставки с сайта: тот же файл, что у калькулятора на сайте; сеть только у страницы панели, без разрешений Orca */
  var RK = 'smeta3d·rates', SITE_URLS = ['https://raw.githubusercontent.com/NeroArtNuar/smeta3d/main/rates.dat', 'https://raw.githubusercontent.com/NeroArtNuar/smeta3d/main/rates.default.dat'];
  var SITE_MONEY = ['minOrder','taxRev','vat','rate','setupMin','plateMin','kwh','twoRate','kwhNight','nightFrom','nightTo','risk','waste','rushPct','presets','insertPrice','cadRate'];
  var siteBusy = false, siteErr = '';
  function decRates(t){ var s = atob(String(t).trim()), b = new Uint8Array(s.length); for (var i = 0; i < s.length; i++) b[i] = s.charCodeAt(i) ^ (RK.charCodeAt(i % RK.length) & 255); return JSON.parse(new TextDecoder().decode(b)); }
  function siteOn(){ return !!(S && S.useSite !== false && S.site && S.site.money); }
  function M(){ if (!siteOn()) return S.money; var o = {}, k; for (k in S.money) o[k] = S.money[k]; SITE_MONEY.forEach(function(k){ if (S.site.money[k] !== undefined) o[k] = S.site.money[k]; }); return o; }
  function words(s){ return ' ' + String(s || '').toLowerCase().replace(/[^0-9a-zа-яё]+/g, ' ').trim() + ' '; }
  /** принтер сайта для профиля Orca: совпадает модель с цифрами (d600, k1) и не меньше половины слов названия */
  function sitePrinter(){
    if (!siteOn()) return null; var w = words(prKey() + ' ' + ((slice && slice.model) || '')), best = null, bs = 0;
    (S.site.printers || []).forEach(function(p){
      var t = words(p.name).trim().split(' ').filter(function(x){ return x.length >= 2; }); if (!t.length) return;
      var hit = t.filter(function(x){ return w.indexOf(' ' + x + ' ') >= 0; }), num = hit.some(function(x){ return /\d/.test(x); }), sc = hit.length / t.length;
      if (num && sc >= 0.5 && sc > bs){ bs = sc; best = p; }
    });
    return best;
  }
  var MAT_ALIAS = { pacf:'pa6cf', pa12cf:'pa6cf', pa6cf:'pa6cf', paht:'pa6cf', pahtcf:'pa6cf', nylon:'pa', pa6:'pa', pa12:'pa', pcabs:'pc', tpu95a:'tpu95a', tpu:'tpu95a', flex:'tpu95a' };
  function siteMat(f){
    if (!siteOn() || !f) return null; var ty = String(f.type || '').toLowerCase().replace(/[^0-9a-z]+/g, ''); if (!ty) return null;
    var key = MAT_ALIAS[ty] || ty, matte = /matte|матов/i.test(f.name || ''), list = (S.site.materials || []).map(function(m){ return { m:m, n:String(m.name).toLowerCase().replace(/\(.*?\)/g, '').replace(/[^0-9a-z]+/g, '') }; });
    var pick = function(fn){ var c = list.filter(fn).sort(function(a, b){ return a.n.length - b.n.length; }); return c.length ? c[0].m : null; };
    return pick(function(x){ return x.n === key + (matte ? 'matte' : ''); }) || pick(function(x){ return x.n === key; }) || pick(function(x){ return x.n.indexOf(key) === 0; });
  }
  function siteFetch(force){
    if (siteBusy || !S || S.useSite === false) return;
    if (!force && S.site && S.site.got && nowMs() - S.site.got < 6 * 3600e3) return;
    if (typeof fetch !== 'function'){ siteErr = 'нет доступа к сети'; renderSite(); return; }
    siteBusy = true; siteErr = ''; renderSite();
    var i = 0;
    (function next(){
      if (i >= SITE_URLS.length){ siteBusy = false; siteErr = 'сайт недоступен'; renderSite(); render(); return; }
      var u = SITE_URLS[i++], first = i === 1;
      fetch(u + '?t=' + Math.floor(Date.now() / 60000), { cache:'no-store' }).then(function(r){ if (!r.ok) throw new Error(r.status); return r.text(); }).then(function(t){
        var f = decRates(t); if (!f || !f.money) throw new Error('bad');
        var prevMk = S.site && S.site.money ? S.site.money.markup : null;
        S.site = { got:Date.now(), at:f.at || null, own:first, money:f.money,
          printers:(f.printers || []).filter(function(p){ return (p.tech || 'fdm') === 'fdm'; }).map(function(p){ return { name:p.name, price:+p.price, life:+p.life, maint:+p.maint, power:+p.power, chamberPower:+p.chamberPower || 0, chamberMin:+p.chamberMin || 0 }; }),
          materials:(f.materials || []).filter(function(m){ return (m.tech || 'fdm') === 'fdm'; }).map(function(m){ return { name:m.name, price:+m.price }; }) };
        if (f.money.markup != null && +f.money.markup !== +prevMk) S.money.markup = +f.money.markup;   // наценка сайта — по умолчанию, кнопки клиентов работают как раньше
        siteBusy = false; siteErr = ''; render(); save();
      }).catch(next);
    })();
  }
  function fmtD(t){ var d = new Date(t); return d.toLocaleDateString('ru-RU', { day:'2-digit', month:'2-digit' }) + ' ' + d.toLocaleTimeString('ru-RU', { hour:'2-digit', minute:'2-digit' }); }
  function renderSite(){
    if (!S || !$('siteBox')) return; var on = S.useSite !== false, st = $('siteSt'), sp = sitePrinter();
    $('useSite').checked = on; $('siteRef').hidden = !on; st.classList.toggle('bad', !!siteErr && on);
    st.textContent = !on ? 'свои ставки' : siteBusy ? 'обновляю…' : siteErr ? (S.site ? siteErr + ', ставки от ' + fmtD(S.site.at || S.site.got) : siteErr + ' — считаю по своим ставкам')
      : S.site ? (S.site.own ? 'от ' + fmtD(S.site.at || S.site.got) : 'стандартные ставки сайта') + (slice ? (sp ? ' · ' + sp.name : ' · этого принтера нет на сайте — свои ставки принтера') : '') : '';
  }
  var SITE_PR = ['pr.price','pr.life','pr.maint','pr.power','pr.chamberPower','pr.chamberMin'];
  function siteKey(k){ return siteOn() && (SITE_MONEY.indexOf(k.replace(/^money\./, '')) >= 0 && k.indexOf('money.') === 0 || (SITE_PR.indexOf(k) >= 0 && !!sitePrinter())); }
  /* готовые ставки для известных принтеров — подставляются, пока вы не поменяли их сами */
  var PRESETS = [
    { re:/d600\s*pro\s*3?\s*hs|d600\s*pro3/i, name:'CreatBot D600 Pro3 HS', note:'ставки вашей мастерской, как на сайте',
      v:{ price:1000000, life:20000, maint:50, power:450, chamberPower:1200, extraMin:10, chamberMin:25 } },
    { re:/k1\s*max/i, name:'Creality K1 Max', note:'ставки примерные', v:{ price:85000, life:5000, maint:15, power:300, chamberPower:0, extraMin:3, chamberMin:0 } },
    { re:/x1\s*-?\s*carbon|x1c|x1e/i, name:'Bambu Lab X1', note:'ставки примерные', v:{ price:150000, life:6000, maint:20, power:200, chamberPower:0, extraMin:2, chamberMin:0 } },
    { re:/p1s|p1p/i, name:'Bambu Lab P1', note:'ставки примерные', v:{ price:75000, life:5000, maint:15, power:150, chamberPower:0, extraMin:2, chamberMin:0 } },
    { re:/bambu.*\ba1\b|\ba1 mini\b/i, name:'Bambu Lab A1', note:'ставки примерные', v:{ price:40000, life:4000, maint:10, power:110, chamberPower:0, extraMin:2, chamberMin:0 } }
  ];
  function presetFor(k){ var t = k + ' ' + ((slice && slice.model) || ''); for (var i = 0; i < PRESETS.length; i++) if (PRESETS[i].re.test(t)) return PRESETS[i]; return null; }
  function plainDefault(p){ var d = S.printer_default; return ['price','life','maint','power'].every(function(k){ return +p[k] === +d[k]; }); }
  function prKey(){ return (slice && slice.printer) || 'Принтер по умолчанию'; }
  function prOwn(){
    var k = prKey(), p = S.printers[k], ps = presetFor(k);
    if (!p || (ps && !p.preset && plainDefault(p))){ p = S.printers[k] = ps ? clone(ps.v) : clone(S.printer_default); if (ps) p.preset = ps.name; }
    if (ps) for (var key in ps.v) if (p[key] == null) p[key] = ps.v[key];   // свои ставки не трогаем, дополняем только пустые поля
    if (p.extraMin == null) p.extraMin = 0; if (p.chamberPower == null) p.chamberPower = 0; if (p.chamberMin == null) p.chamberMin = 0;
    return p;
  }
  function prObj(){
    var p = prOwn(), sp = sitePrinter(); if (!sp) return p;
    var o = {}, k; for (k in p) o[k] = p[k];
    o.price = sp.price; o.life = sp.life; o.maint = sp.maint; o.power = sp.power; o.chamberPower = sp.chamberPower; o.chamberMin = sp.chamberMin; o.siteName = sp.name;
    return o;
  }
  function chamberOn(){ return !!(slice && slice.chamberC > 0); }
  function filObj(name){ if (!S.filaments[name]) S.filaments[name] = clone(S.filament_default); return S.filaments[name]; }
  function filPrice(f){ var sm = siteMat(f); if (sm) return +sm.price || 0; var o = filObj(f.name); return (o.from_orca && f.orcaPrice > 0) ? f.orcaPrice : (+o.price || 0); }
  function getK(k){ var p = k.split('.'), o = p[0] === 'pr' ? prObj() : p[0] === 'money' ? M() : S[p[0]]; return o[p[1]]; }
  function setK(k, v){ if (siteKey(k)) return; var p = k.split('.'), o = p[0] === 'pr' ? prOwn() : S[p[0]]; o[p[1]] = v; }
  /* на столе разные модели → заказ считается комплектами: 1 комплект = всё, что лежит на столе */
  function many(){ return !!(slice && slice.objects && slice.objects.length > 1); }
  function setPcs(){ return many() ? Math.max(1, autoParts) : 1; }
  function U(){ return many() ? 'компл.' : 'шт'; }
  function parts(){ return +S.order.partsOverride > 0 ? Math.round(+S.order.partsOverride) : many() ? 1 : Math.max(1, autoParts); }

  /* экономика та же, что в калькуляторе «Смета 3D-печати»; вес и время стола — из G-code Orca */
  /* «Комплект по количеству»: сколько штук каждой модели нужно на 1 комплект */
  function kitOn(){ return false; } // комплекты — только на сайте
  function nameCount(n){ var mm = /(?:^|[\]_\s-])x(\d{1,3})(?=[_\s.-]|$)/i.exec(n || ''); return mm ? +mm[1] : 0; }
  function need(o){ var v = (S.order.need || {})[o.name]; return v != null && isFinite(+v) ? Math.max(0, Math.round(+v)) : o.copies; }
  /* что печатаем: штуки каждой модели, время станка, граммы по пластикам, число столов */
  /* ---- сроки и тарифы ---- */
  function tms(v){ if (!v) return null; var t = Date.parse(v); return isFinite(t) ? t : null; }
  function fmtT(t){ var d = new Date(t); return d.toLocaleDateString('ru-RU', { weekday:'short', day:'2-digit', month:'2-digit' }) + ' ' + d.toLocaleTimeString('ru-RU', { hour:'2-digit', minute:'2-digit' }); }
  function nowMs(){ return window.__now ? window.__now : Date.now(); }
  /* печать начинается сейчас — время старта нужно только для ночного тарифа; сроки и срочность считаются на сайте */
  function plan(hours){ var now = nowMs(); return { start:now, end:now + hours * 3600e3, mode:'none', dl:null, busy:null }; }
  function nightShare(start, hours){
    var m = M(); if (!m.twoRate || hours <= 0) return 0;
    var a = (+m.nightFrom || 0) % 24, b = (+m.nightTo || 0) % 24, steps = 600, n = 0, dt = hours * 3600e3 / steps;
    for (var i = 0; i < steps; i++){ var h = new Date(start + (i + 0.5) * dt); h = h.getHours() + h.getMinutes() / 60; if (a < b ? (h >= a && h < b) : (h >= a || h < b)) n++; }
    return n / steps;
  }
  function presets(){ if (siteOn() && Array.isArray(S.site.money.presets) && S.site.money.presets.length) return S.site.money.presets; var p = S.money.presets; if (!Array.isArray(p) || !p.length) p = S.money.presets = [{ n:'Розница', v:100 }, { n:'Опт', v:50 }, { n:'Свои', v:30 }]; return p; }

  function job(q, n){
    var list = objs(), per, machineS, plates, gSlot = fils().map(function(){ return 0; }), pcs;
    if (false){
      per = list.map(function(o){ return { o:o, pcs:need(o) * q }; });
      machineS = per.reduce(function(a, x){ return a + x.pcs * (x.o.timeS || 0) / x.o.copies; }, 0);
      plates = Math.max(1, Math.ceil(machineS / Math.max(1, slice.machineS || 1) - 1e-6));
      per.forEach(function(x){ (x.o.gramsBySlot || []).forEach(function(g, i){ if (i < gSlot.length) gSlot[i] += g / x.o.copies * x.pcs; }); });
      pcs = per.reduce(function(a, x){ return a + x.pcs; }, 0);
    } else {
      var share = q / n;
      per = list.map(function(o){ return { o:o, pcs:o.copies * share }; });
      machineS = share * (slice.machineS || 0); plates = Math.ceil(q / n);
      gSlot = fils().map(function(f){ return f.grams * share; }); pcs = q * setPcs();
    }
    return { per:per, machineS:machineS, plates:plates, gSlot:gSlot, pcs:pcs };
  }
  function calc(qty){
    var m = M(), pr = prObj(), n = parts(), q = Math.max(1, Math.round(qty || 1));
    var J = job(q, n), plates = J.plates, share = q / n, waste = 1 + (+m.waste || 0) / 100, ch = chamberOn();
    var machineH = J.machineS / 3600 + plates * ((+pr.extraMin || 0) + (ch ? +pr.chamberMin || 0 : 0)) / 60;
    var mat = 0, gNet = 0, gTot = 0, perFil = [];
    fils().forEach(function(f, i){ var g = J.gSlot[i] || 0, gt = g * waste, price = filPrice(f), c = gt / 1000 * price; mat += c; gNet += g; gTot += gt; perFil.push({ f:f, g:g, gt:gt, price:price, cost:c }); });
    var mach = machineH * ((+pr.price || 0) / Math.max(1, +pr.life || 1) + (+pr.maint || 0));
    var watts = (+pr.power || 0) + (ch ? +pr.chamberPower || 0 : 0);
    var P = plan(machineH), kwhUsed = machineH * watts / 1000, fn = nightShare(P.start, machineH);
    var energy = kwhUsed * ((1 - fn) * (+m.kwh || 0) + fn * (m.twoRate ? +m.kwhNight || 0 : +m.kwh || 0));
    var rush = P.mode === 'rush' ? (+m.rushPct || 0) / 100 : 0;
    var plateLab = plates * (+m.plateMin || 0) / 60 * (+m.rate || 0), postLab = J.pcs * (+m.postMin || 0) / 60 * (+m.rate || 0);
    var labor = plateLab + postLab + (+m.setupMin || 0) / 60 * (+m.rate || 0);
    var extraPer = J.pcs * ((+m.inserts || 0) * (+m.insertPrice || 0) + (+m.paint || 0));
    var extra = extraPer + (+m.cadH || 0) * (+m.cadRate || 0) + (+m.packaging || 0);
    var p = Math.min(0.6, Math.max(0, (+m.risk || 0) / 100)), risk = (mat + mach + energy + plateLab) * p / (1 - p);
    var cost = mat + mach + energy + labor + extra + risk;
    var byMarkup = cost * (1 + (+m.markup || 0) / 100) * (1 + (+m.adjust || 0) / 100) * (1 + rush);
    var net = Math.max(byMarkup, +m.minOrder || 0), t = Math.min(0.9, Math.max(0, (+m.taxRev || 0) / 100));
    var noVat = net / (1 - t), client = noVat * (1 + (+m.vat || 0) / 100);
    return { q:q, n:n, J:J, watts:watts, plan:P, kwhUsed:kwhUsed, night:fn, rush:rush, plates:plates, machineH:machineH, gNet:gNet, gTot:gTot, perFil:perFil, gPart: gNet / q,
             mat:mat, mach:mach, energy:energy, labor:labor, plateLab:plateLab, postLab:postLab, extraPer:extraPer, share:share, waste:waste, extra:extra, risk:risk, cost:cost, byMarkup:byMarkup, net:net,
             minApplied: byMarkup < (+m.minOrder || 0), tax:noVat - net, vatAmt:client - noVat, client:client, profit:net - cost };
  }

  function objs(){ return (slice && slice.objects) || []; }
  /* Делим смету заказа между моделями: пластик — по их весу и цене пластика, станок, электричество и работа
     со столом — по времени печати, ручная работа и комплектующие — по числу штук. Наценка, налоги и
     минимальный заказ ложатся пропорционально себестоимости, поэтому сумма по моделям = итог. */
  function byModel(r){
    var per = r.J.per; if (!per.length) return [];
    var tSum = per.reduce(function(a, x){ return a + x.pcs * (x.o.timeS || 0) / x.o.copies; }, 0) || 1;
    var direct = r.mat + r.mach + r.energy + r.plateLab;
    var rows = per.map(function(x){
      var o = x.o, pcs = x.pcs, k = pcs / o.copies;
      var mat = 0; fils().forEach(function(f, i){ var g = (o.gramsBySlot || [])[i] || 0; mat += g * k * r.waste / 1000 * filPrice(f); });
      var ft = k * (o.timeS || 0) / tSum, fp = r.J.pcs > 0 ? pcs / r.J.pcs : 0;
      var mach = r.mach * ft, en = r.energy * ft, plate = r.plateLab * ft;
      var labor = plate + r.postLab * fp + (r.labor - r.plateLab - r.postLab) * ft;
      var extra = r.extraPer * fp + (r.extra - r.extraPer) * ft;
      var risk = direct > 0 ? r.risk * (mat + mach + en + plate) / direct : 0;
      var cost = mat + mach + en + labor + extra + risk;
      return { o:o, pcs:pcs, cost:cost, gPc:o.grams / o.copies, tPc:(o.timeS || 0) / o.copies };
    });
    rows.forEach(function(x){ x.client = r.cost > 0 ? r.client * x.cost / r.cost : 0; x.unit = x.pcs > 0 ? x.client / x.pcs : 0; });
    return rows;
  }
  function fillFromNames(force){ S.order.need = S.order.need || {}; objs().forEach(function(o){ var c = nameCount(o.name); if (c && (force || S.order.need[o.name] == null)) S.order.need[o.name] = c; }); }
  function heat(t){ var a = [42,161,152], b = [224,166,59], c = [226,86,110], u = t < .5 ? a : b, v = t < .5 ? b : c, k = t < .5 ? t * 2 : (t - .5) * 2;
    return 'rgb(' + [0,1,2].map(function(i){ return Math.round(u[i] + (v[i] - u[i]) * k); }).join(',') + ')'; }
  var hlIdx = -1;
  function drawMap(bm){
    var svg = $('plateMap'), bed = slice.bed, any = bm.some(function(x){ return (x.o.boxes || []).length; });
    svg.hidden = $('heatLeg').hidden = !(bed && any); if (svg.hidden){ svg.innerHTML = ''; return; }
    var W = bed[2] - bed[0], H = bed[3] - bed[1], us = bm.map(function(x){ return x.unit; }), lo = Math.min.apply(null, us), hi = Math.max.apply(null, us);
    svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    var out = '';
    bm.forEach(function(x, i){ var t = hi > lo ? (x.unit - lo) / (hi - lo) : 0;
      (x.o.boxes || []).forEach(function(b){ out += '<rect class="m' + (i === hlIdx ? ' hl' : '') + '" data-m="' + i + '" x="' + (b[0] - bed[0]) + '" y="' + (bed[3] - b[3]) + '" width="' + Math.max(2, b[2] - b[0]) + '" height="' + Math.max(2, b[3] - b[1]) + '" rx="2" fill="' + heat(t) + '"><title>' + esc(x.o.name) + ': ' + rub(x.unit) + ' за шт</title></rect>'; }); });
    svg.innerHTML = out;
  }
  function highlight(i, scroll){
    hlIdx = (hlIdx === i) ? -1 : i;
    document.querySelectorAll('[data-m]').forEach(function(el){ el.classList.toggle('hl', +el.dataset.m === hlIdx); });
    if (scroll && hlIdx >= 0){ var row = document.querySelector('.mdl[data-m="' + hlIdx + '"]'); if (row && row.scrollIntoView) row.scrollIntoView({ block:'nearest' }); }
  }
  var notifiedKey = null;
  function maybeNotify(r){
    if (status !== 'fresh' || !slice || slice.mtime === notifiedKey) return;
    notifiedKey = slice.mtime;
    var bm = byModel(r), t = 'Смета: ' + rub(r.client);
    if (bm.length > 1){ var top = bm.slice().sort(function(a, b){ return b.client - a.client; })[0]; t += ' · ' + bm.length + ' ' + plural(bm.length, 'модель', 'модели', 'моделей') + ' · дороже всех ' + top.o.name + ' (' + rub(top.client) + ')'; }
    else t += ' · ' + grams(r.gNet) + ' · ' + dur(r.machineH * 3600);
    // в шрифте уведомлений Orca нет знака ₽ и неразрывного пробела
    bridge.postMessage({ command:'notify', key:slice.mtime, text:t.replace(/\s?₽/g, ' руб.').replace(/\u00a0/g, ' ') });
  }
  function plural(n, a, b, c){ var m10 = n % 10, m100 = n % 100; return m10 === 1 && m100 !== 11 ? a : m10 >= 2 && m10 <= 4 && (m100 < 12 || m100 > 14) ? b : c; }
  function pcsTxt(v){ return Math.abs(v - Math.round(v)) < 1e-6 ? nf(v, 0) : nf(v, 1); }

  function renderStatus(){
    var box = $('status'), t = $('statusTxt'), when = slice ? new Date(slice.mtime * 1000).toLocaleTimeString('ru-RU', { hour:'2-digit', minute:'2-digit' }) : '';
    var st = slice ? status : (status === 'slicing' ? 'slicing' : 'none');
    box.className = 'status ' + st;
    var sub = slice ? '<span class="sub" title="' + esc(slice.printer + ' · ' + slice.process) + '">' + esc(short(slice.printer)) + ' · ' + esc(slice.process) + '</span>' : '';
    t.innerHTML = st === 'slicing' ? '<b>Нарезается…</b>' + sub
      : st === 'stale' ? '<b>Нарежьте заново</b> — ' + esc(staleReason || 'модель изменилась') + sub
      : st === 'fresh' ? '<b>Актуально</b> · нарезано в ' + when + sub
      : '<b>Нет нарезки</b>';
    $('err').hidden = !err; $('err').textContent = err || '';
  }
  /* списки (пластики, модели) перерисовываются целиком — возвращаем фокус и курсор в поле, где печатают */
  function render(){
    var a = document.activeElement, keep = null;
    if (a && a.dataset && (a.dataset.fil != null || a.dataset.need != null)){
      keep = { attr: a.dataset.fil != null ? 'data-fil' : 'data-need', v: a.dataset.fil != null ? a.dataset.fil : a.dataset.need, s: a.selectionStart, e: a.selectionEnd };
    }
    renderInner();
    if (keep){
      var b = document.querySelector('[' + keep.attr + '="' + (window.CSS && CSS.escape ? CSS.escape(keep.v) : keep.v) + '"]');
      if (b && b !== document.activeElement){ b.focus(); try { if (keep.s != null) b.setSelectionRange(keep.s, keep.e); } catch(x){} }
    }
  }
  function renderInner(){
    if (!S) return;
    renderStatus();
    var has = !!(slice && slice.grams > 0);
    $('emptyBox').hidden = has; $('hero').hidden = $('main').hidden = !has;
    if (!has) return;
    var dimNow = status === 'stale' || status === 'slicing';
    $('hero').classList.toggle('dim', dimNow); $('modelList').classList.toggle('dim', dimNow);
    var keys = prKey() + '|' + fils().map(function(f){ return f.name; }).join('|'), force = keys !== lastKeys; lastKeys = keys;
    renderSite();
    document.querySelectorAll('[data-k]').forEach(function(el){ el.disabled = siteKey(el.dataset.k); el.title = el.disabled ? 'Задаётся на сайте «Смета 3D» в режиме «Бизнес»' : ''; });
    document.querySelectorAll('[data-quick]').forEach(function(box){ var dis = siteKey(box.dataset.quick); box.querySelectorAll('button').forEach(function(b){ b.disabled = dis; }); });
    document.querySelectorAll('[data-k]').forEach(function(el){ if (force || document.activeElement !== el){ var v = getK(el.dataset.k); if (el.type === 'checkbox') el.checked = !!v; else el.value = (el.id === 'parts' && !v) ? '' : (v == null ? '' : v); } });
    document.querySelectorAll('[data-quick]').forEach(function(box){ var v = getK(box.dataset.quick); box.querySelectorAll('button').forEach(function(b){ b.classList.toggle('on', +b.dataset.v === +v); }); });
    var r = calc(S.order.qty), m = M();
    // главный блок
    $('total').textContent = rub(r.client);
    var ready = (r.plan.mode !== 'none' || r.plan.busy) ? ' · готово ' + fmtT(r.plan.end) : '';
    $('summary').textContent = (r.q > 1 ? r.q + ' ' + U() + ' по ' + rub(r.client / r.q) : '1 ' + U()) + (many() ? ' (' + pcsTxt(r.J.pcs) + ' шт)' : '') + ' · ' + grams(r.gNet) + ' · ' + dur(r.machineH * 3600) + (r.plates > 1 ? ' · ' + r.plates + ' стола' : '') + ready;
    var taxes = r.tax + r.vatAmt, total = Math.max(0.01, r.client);
    $('bar').innerHTML = [[r.cost, 'var(--c-cost)'], [Math.max(0, r.profit), 'var(--c-profit)'], [taxes, 'var(--c-tax)']].map(function(x){ return '<span style="width:' + (x[0] / total * 100) + '%;background:' + x[1] + '"></span>'; }).join('');
    $('legend').innerHTML = '<span><i style="background:var(--c-cost)"></i>Себестоимость <b>' + rub(r.cost) + '</b></span><span><i style="background:var(--c-profit)"></i>Прибыль <b>' + rub(r.profit) + '</b></span>' + (taxes > 0.005 ? '<span><i style="background:var(--c-tax)"></i>Налоги <b>' + rub(taxes) + '</b></span>' : '');
    // наценка: кнопки типовых клиентов
    $('mkPresets').innerHTML = presets().map(function(p, i){ return '<button type="button" class="pre' + (+p.v === +m.markup ? ' on' : '') + '" data-mk="' + i + '">' + esc(p.n) + ' ' + p.v + '%</button>'; }).join('');
    if (!(document.activeElement && document.activeElement.dataset && document.activeElement.dataset.pre != null))
      $('mkEdit').innerHTML = presets().map(function(p, i){ return '<span class="inp"><input type="text" data-pre="' + i + '" data-f="n" value="' + esc(p.n) + '" aria-label="Название кнопки ' + (i + 1) + '"></span><span class="inp"><input type="number" min="0" step="5" data-pre="' + i + '" data-f="v" value="' + p.v + '" aria-label="Наценка кнопки ' + (i + 1) + '"><em>%</em></span>'; }).join('');
    // день/ночь
    $('nightBox').hidden = !m.twoRate; $('kwhLab').textContent = m.twoRate ? 'Дневной тариф' : 'Тариф на электричество';
    // по моделям
    var bm = byModel(r), multi = bm.length > 1, noLabels = !bm.length && autoParts > 1;
    $('secModels').hidden = !(multi || noLabels);
    if (multi){
      var maxU = Math.max.apply(null, bm.map(function(x){ return x.client; })) || 1;
      $('modelList').innerHTML = bm.map(function(x){
        var cnt = kitOn() ? '<span class="inp need"><input type="text" inputmode="numeric" data-need="' + esc(x.o.name) + '" value="' + need(x.o) + '" aria-label="Нужно штук ' + esc(x.o.name) + '"><em>шт</em></span>' + (r.q > 1 ? '<span class="cp">×' + r.q + '</span>' : '')
          : '<span class="cp">× ' + pcsTxt(x.pcs) + ' шт</span>';
        return '<div class="mdl" data-m="' + bm.indexOf(x) + '"><div class="hd"><span class="nm" title="' + esc(x.o.name) + '">' + esc(x.o.name) + '</span>' + cnt + '<span class="pr">' + rub(x.unit) + '</span></div>' +
          '<div class="sub"><span>' + grams(x.gPc) + ' · ' + dur(x.tPc) + '</span><span>всего ' + rub(x.client) + '</span></div>' +
          '<div class="mb"><span style="width:' + (x.client / maxU * 100) + '%"></span></div></div>';
      }).join('');
      $('sModels').textContent = bm.length + ' ' + plural(bm.length, 'модель', 'модели', 'моделей');
      drawMap(bm);
      var hasNames = objs().some(function(o){ return nameCount(o.name) > 0; });
      $('modelHint').textContent = (kitOn() ? 'Комплект ' + r.J.pcs / r.q + ' шт: время и пластик считаются по каждой детали, столов ≈ ' + r.plates + '. Точнее всего, если на столе лежит по одной детали каждого вида. ' : '') +
        (slice.overheadG > 0.05 ? 'Башня, продувка и юбка (' + grams(slice.overheadG) + ' на стол) разделены между моделями пропорционально их пластику.' : '');
    } else if (noLabels){
      $('modelList').innerHTML = ''; $('sModels').textContent = ''; $('plateMap').innerHTML = ''; $('plateMap').hidden = $('heatLeg').hidden = true;
      $('modelHint').textContent = 'Чтобы видеть цену каждой модели, включите в профиле процесса «Подписывать объекты» (Прочее → G-code → Label objects) и нарежьте заново.';
    }
    // заказ
    $('qtyLab').textContent = many() ? 'Комплектов' : 'Тираж, шт'; $('qtyUnit').textContent = U();
    $('partsLab').textContent = many() ? 'Комплектов на столе' : 'Деталей на столе';
    $('partsAuto').textContent = 'авто ' + (many() ? 1 : autoParts);
    $('tiersLab').textContent = many() ? 'Цена комплекта при тираже' : 'Цена за штуку при тираже';
    $('partsHint').textContent = kitOn() ? 'комплект задаётся в разделе «По моделям»' : many() ? (bm.length > 3 ? '1 комплект = все ' + setPcs() + ' шт со стола (' + bm.length + ' ' + plural(bm.length, 'модель', 'модели', 'моделей') + ')' : '1 комплект = ' + bm.map(function(x){ return x.o.copies + ' × ' + x.o.name; }).join(' + ')) : r.n > 1 ? 'на 1 деталь ' + grams(slice.grams / r.n) + ', ' + dur((slice.machineS || 0) / r.n) : '';
    $('sOrder').textContent = r.q + ' ' + U() + ' · наценка ' + (m.markup || 0) + '%';
    // пластики
    var fl = $('filList'); fl.innerHTML = r.perFil.map(function(x, i){
      var o = filObj(x.f.name), sm = siteMat(x.f), canOrca = x.f.orcaPrice > 0 && !sm;
      return '<div class="fil"><div class="hd"><span class="nm" title="' + esc(x.f.name) + '">' + (fils().length > 1 ? x.f.slot + '. ' : '') + esc(short(x.f.name)) + '</span><span class="g">' + grams(x.g) + (r.q > 1 || r.n > 1 ? '' : '') + '</span></div>' +
        '<div class="row2"><span class="inp"><input type="text" inputmode="decimal" data-fil="' + i + '" value="' + (sm ? +sm.price : o.from_orca && canOrca ? x.f.orcaPrice : (+o.price || 0)) + '"' + (sm || (o.from_orca && canOrca) ? ' disabled' : '') + ' aria-label="Цена пластика ' + esc(short(x.f.name)) + '"><em>₽/кг</em></span><span class="sum2">' + rub(x.cost) + '</span></div>' +
        (sm ? '<span class="site-note">цена с сайта: ' + esc(sm.name) + '</span>' : '') + (canOrca ? '<label class="chk"><input type="checkbox" data-filorca="' + i + '"' + (o.from_orca ? ' checked' : '') + '> цена из профиля Orca: ' + nf(x.f.orcaPrice, 2) + '</label>' : '') + '</div>';
    }).join('');
    $('sFil').textContent = rub(r.mat);
    $('wasteHint').textContent = slice.changes > 0 ? 'Продувка при смене пластика (' + slice.changes + ' смен) уже входит в вес Orca.' : '';
    var orcaCost = slice.orcaCost != null && slice.grams > 0 ? slice.orcaCost * r.gNet / slice.grams : null;
    $('filCmp').innerHTML = orcaCost != null ? '<span>В Orca' + (r.q > 1 ? ' за ' + r.q + ' ' + U() : '') + ' (без запаса)</span><b>' + nf(orcaCost, 2) + '</b>' : '';
    // себестоимость
    var parts_ = [['Пластик', r.mat, '#3fb27f'], ['Амортизация, обслуживание', r.mach, '#5b8fd6'], [(m.twoRate && r.night > 0.005 ? 'Электроэнергия (' + nf(r.kwhUsed, 1) + ' кВт·ч, ночью ' + nf(r.night * 100, 0) + '%)' : 'Электроэнергия (' + nf(r.kwhUsed, 1) + ' кВт·ч)'), r.energy, '#e0a63b'], ['Работа', r.labor, '#a088e6'], ['Комплектующие, услуги', r.extra, '#e57aa2'], ['Резерв на брак', r.risk, '#e2566e']];
    var rows = parts_.filter(function(x){ return x[1] > 0.005; }).map(function(x){ return '<div class="row"><span class="l"><i style="background:' + x[2] + '"></i>' + x[0] + '</span><span class="pc">' + nf(x[1] / Math.max(0.01, r.cost) * 100, 0) + '%</span><span class="r">' + rub(x[1]) + '</span></div>'; }).join('');
    rows += '<div class="row b"><span class="l">Себестоимость</span><span class="r">' + rub(r.cost) + '</span></div>';
    rows += '<div class="row"><span class="l">Наценка ' + (m.markup || 0) + '%' + (+m.adjust ? ', ' + (m.adjust > 0 ? 'срочность +' : 'скидка ') + m.adjust + '%' : '') + (r.minApplied ? ' (минимальный заказ)' : '') + '</span><span class="r">' + rub(r.net - r.cost) + '</span></div>';
    if (r.tax > 0.005) rows += '<div class="row"><span class="l">Налог ' + m.taxRev + '%</span><span class="r">' + rub(r.tax) + '</span></div>';
    if (r.vatAmt > 0.005) rows += '<div class="row"><span class="l">НДС ' + m.vat + '%</span><span class="r">' + rub(r.vatAmt) + '</span></div>';
    rows += '<div class="row b ' + (r.profit >= 0 ? 'pos' : 'neg') + '"><span class="l">Прибыль' + (r.net > 0 ? ' · маржа ' + nf(r.profit / r.net * 100, 0) + '%' : '') + '</span><span class="r">' + rub(r.profit) + '</span></div>';
    $('rows').innerHTML = rows; $('sCost').textContent = rub(r.cost) + ' → ' + rub(r.profit);
    // тиражи
    var u1 = calc(1).client;
    $('tiers').innerHTML = [1, 5, 10, 25, 50, 100].map(function(q){ var u = calc(q).client / q, d = (1 - u / u1) * 100;
      return '<button type="button" class="tier' + (q === r.q ? ' on' : '') + '" data-q="' + q + '"><div class="q">' + q + ' ' + U() + '</div><div class="p">' + rub(u) + '</div><div class="d">' + (d >= 1 ? '−' + nf(d, 0) + '%' : '&nbsp;') + '</div></button>'; }).join('');
    // принтер, работа, налоги
    $('sPr').textContent = short(prKey());
    var prx = prObj(), ch = chamberOn();
    $('fChP').hidden = $('fChM').hidden = !(ch || +prx.chamberPower > 0);
    $('prHint').textContent = 'Ставки запоминаются для профиля «' + prKey() + '». Время станка ' + dur(r.machineH * 3600) + ' = время Orca + ' + ((+prx.extraMin || 0) + (ch ? +prx.chamberMin || 0 : 0)) + ' мин на стол. Мощность ' + nf(r.watts, 0) + ' Вт' + (ch ? ' (камера ' + nf(slice.chamberC, 0) + ' °C)' : ', камера не греется') + '.';
    var ps = presetFor(prKey());
    $('prPreset').textContent = prx.siteName ? 'Ставки принтера с сайта: ' + prx.siteName + '. Меняются на сайте в режиме «Бизнес». Доп. минуты на стол — здесь.' : prx.preset ? 'Ставки из готового профиля ' + prx.preset + (ps && ps.note ? ': ' + ps.note : '') + '.' : '';
    $('sWork').textContent = rub(r.labor + r.extra);
    $('sTax').textContent = (m.taxRev || 0) + '%' + (+m.vat ? ' + НДС ' + m.vat + '%' : '') + (+m.adjust ? ' · ' + (m.adjust > 0 ? '+' : '') + m.adjust + '%' : '');
    maybeNotify(r);
    // разделы, открытые в прошлый раз
    document.querySelectorAll('details[data-sec]').forEach(function(d){ if (!d.dataset.init){ d.dataset.init = 1; d.open = (S.ui && S.ui.open || []).indexOf(d.dataset.sec) >= 0; } });
  }
  function kpText(r){
    var L = [], mats = fils().map(function(f){ return short(f.name); }).join(', ');
    L.push('Коммерческое предложение на 3D-печать от ' + new Date().toLocaleDateString('ru-RU'), '');
    L.push('Изделие: ' + ((S.order.name || '').trim() || 'по согласованной модели'), 'Технология: FDM (печать пластиковой нитью)', 'Материал: ' + mats, 'Масса 1 шт: ≈ ' + nf(r.gPart, r.gPart < 10 ? 1 : 0) + ' г', 'Тираж: ' + r.q + ' ' + U() + (many() ? ' (' + pcsTxt(r.J.pcs) + ' шт)' : ''), '');
    var bm = byModel(r);
    if (bm.length > 1){
      L.splice(L.length - 3, 1);
      L.push('Состав заказа:');
      bm.forEach(function(x){ L.push('  ' + x.o.name + ' — ' + pcsTxt(x.pcs) + ' шт × ' + rub(x.unit) + ' = ' + rub(x.client) + ' (≈ ' + nf(x.gPc, x.gPc < 10 ? 1 : 0) + ' г/шт)'); });
      L.push('');
    }
    if (r.q > 1) L.push('Цена за 1 ' + U() + ': ' + rub(r.client / r.q));
    L.push('Итого: ' + rub(r.client));
    if (r.plan.mode !== 'none' || r.plan.busy) L.push('Срок готовности: ' + fmtT(r.plan.end) + (r.rush ? ' (срочный заказ)' : ''));
    if (r.vatAmt > 0.005) L.push('В том числе НДС ' + M().vat + '%: ' + rub(r.vatAmt));
    L.push('', many() ? 'Цена комплекта при другом тираже:' : 'Цена за штуку при другом тираже:');
    [1, 5, 10, 25, 50, 100].forEach(function(q){ if (q !== r.q){ var o = calc(q); L.push('  ' + q + ' ' + U() + ' — ' + rub(o.client / q) + ' за ' + U() + ', всего ' + rub(o.client)); } });
    return L.join('\n');
  }
  var saveT = null, pollT = null;
  function save(){ clearTimeout(saveT); saveT = setTimeout(function(){ bridge.postMessage({ command:'save', settings:S }); }, 400); }
  function clamp(el, v){ if (el.min !== '' && v < +el.min) v = +el.min; if (el.max !== '' && v > +el.max) v = +el.max; return v; }

  document.addEventListener('input', function(e){
    var el = e.target;
    if (el.dataset && el.dataset.pre != null){ var pp = presets()[+el.dataset.pre]; if (pp){ if (el.dataset.f === 'n') pp.n = el.value; else { var pv = parseFloat(el.value); if (isFinite(pv) && pv >= 0) pp.v = pv; } render(); save(); } return; }
    if (el.dataset && el.dataset.need != null){ var nv = parseInt(el.value, 10); if (isFinite(nv) && nv >= 0){ S.order.need = S.order.need || {}; S.order.need[el.dataset.need] = nv; render(); save(); } return; }
    if (el.dataset && el.dataset.fil != null){ var f = fils()[+el.dataset.fil], v = parseFloat(String(el.value).replace(',', '.')); if (f && isFinite(v)){ filObj(f.name).price = Math.max(0, v); render(); save(); } return; }
    if (!el.dataset || !el.dataset.k) return;
    if (el.type === 'checkbox'){ setK(el.dataset.k, el.checked); render(); save(); return; }
    var v = el.type === 'number' ? parseFloat(el.value) : el.value;
    if (el.type === 'number'){ if (!isFinite(v)){ if (el.id === 'parts' && el.value === '') v = 0; else return; } v = clamp(el, v); }
    setK(el.dataset.k, v); render(); save();
  });
  document.addEventListener('change', function(e){
    var el = e.target;
    if (el.id === 'useSite'){ S.useSite = el.checked; if (el.checked) siteFetch(true); render(); save(); return; }
    if (el.id === 'kitOn'){ S.order.kit = el.checked; if (el.checked && !Object.keys(S.order.need || {}).length) fillFromNames(); render(); save(); return; }
    if (el.dataset && el.dataset.filorca != null){ var f = fils()[+el.dataset.filorca]; if (f){ filObj(f.name).from_orca = el.checked; render(); save(); } return; }
    if (el.dataset && el.dataset.k && el.type === 'number'){ var v = getK(el.dataset.k); if (el.id !== 'parts' || v) el.value = v; }
  });
  document.addEventListener('toggle', function(e){
    var d = e.target; if (!d.dataset || !d.dataset.sec || !S || !d.dataset.init) return;
    S.ui = S.ui || { open: [] }; var a = S.ui.open || [], i = a.indexOf(d.dataset.sec);
    if (d.open && i < 0) a.push(d.dataset.sec); if (!d.open && i >= 0) a.splice(i, 1); S.ui.open = a; save();
  }, true);
  function copy(btnMsg){
    var ta = $('kp'), done = function(ok){ $(btnMsg).textContent = ok ? 'Скопировано' : 'Откройте «Текст КП» и нажмите Ctrl+C'; setTimeout(function(){ $(btnMsg).textContent = ''; }, 2500); };
    try { navigator.clipboard.writeText(ta.value).then(function(){ done(true); }, function(){ ta.select(); var ok = false; try { ok = document.execCommand('copy'); } catch(x){} done(ok); }); }
    catch(x){ ta.select(); var ok = false; try { ok = document.execCommand('copy'); } catch(y){} done(ok); }
  }
  document.addEventListener('click', function(e){
    var t = e.target.closest ? e.target.closest('[data-q]') : null;
    if (t){ S.order.qty = +t.dataset.q; render(); save(); return; }
    var qb = e.target.closest ? e.target.closest('[data-quick] button') : null;
    if (qb){ setK(qb.parentNode.dataset.quick, +qb.dataset.v); render(); save(); return; }
    var mk = e.target.closest ? e.target.closest('[data-mk]') : null;
    if (mk){ S.money.markup = +presets()[+mk.dataset.mk].v; render(); save(); return; }
    var mm = e.target.closest ? e.target.closest('[data-m]') : null;
    if (mm && !(e.target.dataset && e.target.dataset.need != null)){ highlight(+mm.dataset.m, mm.tagName.toLowerCase() === 'rect'); return; }
    if (e.target.id === 'busyNow'){ prOwn().busyUntil = ''; render(); save(); return; }
    if (e.target.id === 'busyAfter'){ var d = new Date(+e.target.dataset.end); d.setMinutes(d.getMinutes() - d.getTimezoneOffset()); prOwn().busyUntil = d.toISOString().slice(0, 16); render(); save(); return; }
    if (e.target.id === 'kitNames'){ fillFromNames(true); render(); save(); return; }
    if (e.target.id === 'refresh') bridge.postMessage({ command:'refresh' });
    if (e.target.id === 'siteRef'){ siteFetch(true); return; }
  });
  bridge.onMessage(function(msg){
    if (!msg || msg.command !== 'state') return;
    if (msg.settings) S = msg.settings;
    S.ui = S.ui || { open: ['order', 'filaments'] };
    if (msg.notifyInfo != null) $('noteInfo').textContent = msg.notifyInfo ? 'Уведомление в Orca: ' + msg.notifyInfo : '';
    clearTimeout(pollT); if (msg.waiting) pollT = setTimeout(function(){ bridge.postMessage({ command:'poll' }); }, 1000);
    slice = msg.slice || null; autoParts = Math.max(1, msg.parts || 1);
    if (slice && slice.objects && slice.objects.length) autoParts = slice.objects.reduce(function(a, o){ return a + (o.copies || 1); }, 0);
    if (!S.ui.modelsSeen){ S.ui.modelsSeen = true; S.ui.open = (S.ui.open || []).concat(['models']); } err = msg.error || null; status = msg.status || (slice ? 'fresh' : 'none'); staleReason = msg.staleReason || '';
    render(); siteFetch(false);
  });
  window.__smeta = { plan: function(h){ return plan(h); }, calc: function(q){ return calc(q); }, byModel: function(q){ return byModel(calc(q)); }, state: function(){ return { S:S, slice:slice, parts:parts(), status:status, site:siteOn(), sitePrinter:sitePrinter() }; } };
  bridge.postMessage({ command:'hello' });
})();
</script>

"""


class SmetaPanel(orca.script.ScriptPluginCapabilityBase):
    panel = None
    settings = None
    last = None
    error = None
    status = "none"       # none | slicing | fresh | stale
    stale_reason = ""
    slice_started = 0.0   # когда началась нарезка — G-code должен быть новее
    wait_tries = 0        # сколько раз страница переспросила, пока Orca дописывает G-code
    waiting = False       # нарезка закончена, ждём, пока Orca допишет G-code

    def get_name(self):
        return PLUGIN_TITLE

    def on_load(self):
        self.settings = load_settings(self)
        if self.settings.get("auto_open", True):
            try:
                self.open_panel()
            except Exception as e:  # окно Orca ещё может быть не готово
                print("Smeta 3D: панель откроется по запуску плагина:", e)

    def execute(self):
        if self.settings is None:
            self.settings = load_settings(self)
        self.open_panel()
        self.refresh(quiet=True)
        return orca.ExecutionResult.success(PLUGIN_TITLE + ": панель открыта")

    def open_panel(self):
        if self.panel is not None and self.panel.is_open():
            self.panel.show()
            return
        self.panel = orca.host.ui.create_dock_panel(
            html=PAGE, title=PLUGIN_TITLE, width=360, height=640,
            on_message=self.on_message, on_close=self.on_close, dock="right")

    def on_close(self):
        self.panel = None

    def state(self):
        return {"command": "state", "settings": self.settings, "slice": self.last, "parts": model_parts(),
                "error": self.error, "status": self.status, "waiting": self.waiting, "notifyInfo": self.notify_info, "staleReason": self.stale_reason,
                "lang": _safe(lambda: orca.host.app_language(), "ru_RU")}

    def post(self):
        if self.panel is not None and self.panel.is_open():
            self.panel.post(self.state())

    def refresh(self, quiet=False):
        try:
            since = self.slice_started - 2 if self.slice_started else 0.0
            path = find_temp_gcode(since)
            if self.waiting and self.wait_tries >= 20 and not (path and _gcode_complete(path)):
                path = find_temp_gcode(0.0)   # Orca не перезаписала файл (стол не менялся) — берём последний свой
            if path and _gcode_complete(path):
                self.last = parse_gcode(path)
                self.error = None if self.last.get("grams") else "В G-code нет веса: проверьте плотность пластика в профиле."
                self.status, self.stale_reason, self.wait_tries, self.waiting = "fresh", "", 0, False
            elif self.waiting:
                # Orca сообщила о конце нарезки, а G-code ещё пишется — страница переспросит через секунду
                self.wait_tries += 1
                if self.wait_tries > 20:
                    self.status, self.wait_tries, self.waiting = ("stale" if self.last else "none"), 0, False
                    self.stale_reason = "не нашёл G-code"
                    self.error = "Не нашёл G-code нарезки во временной папке. Нажмите ↻ или нарежьте ещё раз."
                else:
                    self.status = "slicing"
            elif not quiet:
                self.error = "Не нашёл G-code нарезки. Нарежьте модель ещё раз."
        except PermissionError:
            self.status, self.waiting = ("stale" if self.last else "none"), False
            self.error = "Orca не разрешила плагину читать временную папку. Разрешите доступ, когда спросят, и нарежьте снова."
        except Exception as e:
            self.status, self.waiting = ("stale" if self.last else "none"), False
            self.error = "Не удалось прочитать G-code: %s" % e
        self.post()

    notified_key = None
    notify_info = ""

    def notify(self, key, text):
        """Уведомление в окне Orca после нарезки — один раз на каждую нарезку."""
        if not text or key == self.notified_key:
            return
        self.notified_key = key
        ui = orca.host.ui
        level = None
        try:
            level = ui.NotificationLevel.RegularNotificationLevel
        except Exception:
            pass
        # Orca 2.5: push_notification(notification_level, text, hyper_text="", on_click=None)
        attempts = [
            lambda: ui.push_notification(level, text, hyper_text="Открыть смету", on_click=self._open_from_note),
            lambda: ui.push_notification(level, text),
            lambda: ui.push_notification(text, notification_level=level, hyper_text="Открыть смету", on_click=self._open_from_note),
        ]
        errs = []
        for i, call in enumerate(attempts):
            try:
                res = call()
                self.notify_info = ""
                self.post()
                return
            except Exception as e:
                errs.append("%s: %s" % (type(e).__name__, e))
        self.notify_info = "не показано: " + " | ".join(errs)
        self.post()

    def _open_from_note(self):
        try:
            self.open_panel()
        except Exception as e:
            print("Smeta 3D:", e)
        return True

    def on_message(self, message):
        cmd = (message or {}).get("command")
        if cmd == "hello":
            if self.last is None:
                self.refresh(quiet=True)   # стол мог быть нарезан до открытия панели
            else:
                self.post()
        elif cmd == "refresh":
            self.refresh()
        elif cmd == "poll" and self.waiting:
            self.refresh(quiet=True)
        elif cmd == "save":
            incoming = message.get("settings") or {}
            if isinstance(incoming, dict):
                self.settings.update(incoming)
                try:
                    ok = save_settings(self.settings, self)
                except Exception as e:
                    ok, why = False, str(e)
                else:
                    why = "Orca не дала записать конфиг"
                if not ok:
                    self.error = "Настройки не сохранились: %s" % why
                    self.post()
                elif self.error and self.error.startswith("Настройки не сохранились"):
                    self.error = None
                    self.post()
        elif cmd == "notify":
            self.notify(message.get("key"), message.get("text") or "")
        elif cmd == "hide" and self.panel is not None:
            self.panel.hide()

    # события, после которых смета перестаёт соответствовать модели на столе
    STALE_EVENTS = {
        "ObjectAdded": "добавлена модель", "ObjectDeleted": "удалена модель", "ObjectTransformed": "модель сдвинута или повёрнута",
        "ObjectChanged": "модель изменена", "PresetSelected": "сменён профиль", "PresetSaved": "профиль изменён",
        "PlateSelected": "выбран другой стол", "PlateDeleted": "удалён стол", "ObjectRenamed": "модель переименована",
    }

    def on_lifecycle_event(self, event, ctx):
        try:
            name = getattr(event, "name", str(event))
            if event == orca.LifecycleEvent.SliceStarted:
                self.status, self.slice_started, self.wait_tries, self.waiting = "slicing", time.time(), 0, False
                self.post()
            elif event == orca.LifecycleEvent.SlicingJobComplete:
                if ctx.code == orca.LifecycleEvtCode.Ok:
                    self.waiting = True
                    self.refresh()
                else:
                    self.status = "stale" if self.last else "none"
                    self.stale_reason = "нарезка отменена" if ctx.code == orca.LifecycleEvtCode.Warn else "нарезка с ошибкой"
                    if ctx.code == orca.LifecycleEvtCode.Error and ctx.msg:
                        self.error = "Orca: " + str(ctx.msg)
                    self.post()
            elif name == "GCodeExportFinished" and (self.waiting or self.status == "slicing"):
                self.waiting = True
                self.refresh(quiet=True)
            elif name in ("NewProject", "ProjectOpened", "ProjectClosed"):
                self.last, self.status, self.stale_reason, self.error, self.waiting = None, "none", "", None, False
                self.post()
            elif name in self.STALE_EVENTS:
                if self.last and self.status != "slicing":
                    self.status, self.stale_reason = "stale", self.STALE_EVENTS[name]
                self.post()
        except Exception as e:
            print("Smeta 3D:", e)


def _safe(fn, default):
    try:
        return fn()
    except Exception:
        return default


@orca.plugin
class Smeta3DPlugin(orca.base):
    def register_capabilities(self):
        orca.register_capability(SmetaPanel)
        # Одно разрешение при установке: читать папку G-code предпросмотра Orca. После него плагин
        # больше ничего не спрашивает — других файлов, сети, команд и потоков он не трогает.
        try:
            dirs = model_dirs()
            if dirs and hasattr(orca, "request_permissions"):
                orca.request_permissions(fs_read=dirs)
        except Exception as e:
            print("Smeta 3D: запрос разрешения на чтение не прошёл:", e)
