"""Render site/demo.gif: keel check failing with a counterexample, then
passing after the fix. The output shown is captured from a real run of
./target/release/keel, so rebuild keel first. Needs Pillow.

    python3 tools/demo/render.py
"""
import os, subprocess
from PIL import Image, ImageDraw, ImageFont

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
os.chdir(os.path.join(ROOT, "tools", "demo"))
KEEL = os.path.join(ROOT, "target", "release", "keel")

COLS, ROWS, FS, PAD = 72, 11, 26, 28
BG, FG, DIM = (24, 24, 27), (228, 228, 231), (130, 130, 140)
RED, YEL, GRN, CYAN = (248, 113, 113), (250, 204, 21), (74, 222, 128), (103, 232, 249)
font = ImageFont.truetype("/System/Library/Fonts/Menlo.ttc", FS)
CW = font.getbbox("M")[2]
LH = int(FS * 1.45)
W, H = PAD * 2 + CW * COLS, PAD * 2 + LH * ROWS


def check(f):
    r = subprocess.run([KEEL, "check", f], capture_output=True, text=True)
    return [ln.replace(os.path.join(ROOT, "tools", "demo") + "/", "") for ln in r.stderr.rstrip().splitlines()]


def color(line):
    if "error[" in line:
        return RED
    if line.lstrip().startswith("counterexample"):
        return YEL
    if line.lstrip().startswith("hint"):
        return DIM
    if "proved" in line:
        return GRN
    return FG


frames, durs = [], []
screen = []  # (text, color)


def snap(ms, cursor=False):
    img = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(img)
    for i, (t, c) in enumerate(screen[-ROWS:]):
        x, y = PAD, PAD + i * LH
        if t.startswith("$ "):
            d.text((x, y), "$ ", font=font, fill=CYAN)
            d.text((x + CW * 2, y), t[2:], font=font, fill=FG)
        else:
            d.text((x, y), t, font=font, fill=c)
    if cursor:
        i = min(len(screen), ROWS) - 1
        t = screen[-1][0] if screen else ""
        d.rectangle([PAD + CW * len(t), PAD + i * LH + 4, PAD + CW * (len(t) + 1), PAD + i * LH + LH - 6], fill=FG)
    frames.append(img)
    durs.append(ms)


def type_cmd(cmd):
    screen.append(("$ ", FG))
    snap(400, True)
    for ch in cmd:
        screen[-1] = (screen[-1][0] + ch, FG)
        snap(45, True)
    snap(300, True)


def show(lines, ms_each=60, color_fn=color):
    for ln in lines:
        screen.append((ln, color_fn(ln)))
        snap(ms_each)


src = open("mid.kl").read().rstrip().splitlines()
fixed = open("mid_fixed.kl").read().rstrip().splitlines()

type_cmd("cat mid.kl")
show(src, 40, lambda _: FG)
type_cmd("keel check mid.kl")
show(check("mid.kl"), 120)
snap(3200)

screen.clear()
type_cmd("cat mid_fixed.kl")
show(fixed, 40, lambda ln: GRN if ln not in src else FG)
type_cmd("keel check mid_fixed.kl")
show(check("mid_fixed.kl"), 120)
screen.append(("$ ", FG))
snap(3500, True)

out = os.path.join(ROOT, "site", "demo.gif")
pal = [f.convert("P", palette=Image.ADAPTIVE, colors=16) for f in frames]
pal[0].save(out, save_all=True, append_images=pal[1:], duration=durs, loop=0, optimize=True)
print(out, len(frames), "frames", os.path.getsize(out) // 1024, "KB")
