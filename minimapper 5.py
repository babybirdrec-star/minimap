# =========================================================
#  MiniMapper 30 — MIDI transposer + LED feedback + GUI
#  Joystick (CC30/31) modes, pad transpose, pointer, held-note tracking
# =========================================================
#
#  Mac + Windows.
#    pip install mido python-rtmidi
#    Mac: virtual port "Minimapper" is created automatically.
#    Windows: install loopMIDI, create a port named Minimapper, pick it
#             in To DAW. Your DAW listens to that port.
#
#  MPK Mini PROG 1–4 pair joystick + pad CCs:
#    PROG n:  joystick on MIDI ch n  +  pad CC 0–15 on MIDI ch (n+9)
#    Each PROG has two independent menus:
#      Joystick: MW/PB+Custom CCs | Key Transpose | Pad Transpose | D-Pad/Mouse | PB pass
#      Pads:     Custom CCs | Key Channel | Pad Channel | Keystrokes | Knob Banks | Chord Macros
#        knobs CC20–27 (all PROGs) send the current bank’s outgoing CCs onto the Key Channel
#        CC20–27 on ch 1–4 never arm Chord Learn (noisy knobs)
#
#  Pad notes on ch 10–13 flatten to the Pad Channel (+ pad transpose).
#  LEDs: notes from ch 1–4 show Key Channel; notes from ch 10–13 (or a
#        Pad Channel change) show Pad Channel. Channels 9–16 blink.
#
# =========================================================

import os
import sys
import ctypes
import queue
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import mido

IS_MAC = sys.platform == "darwin"
IS_WIN = sys.platform == "win32"
VIRT_CREATE = "(virtual Minimapper)"


def _norm_midi_name(name):
    return "".join(ch for ch in (name or "").lower() if ch.isalnum())


def is_mpk_name(name):
    n = _norm_midi_name(name)
    return "mpkmini" in n


def is_loop_name(name):
    n = _norm_midi_name(name)
    return any(tag in n for tag in (
        "loopmidi", "minimapper", "midiyoke", "loopbe", "virtualmidi", "loopbe1",
    ))


def list_midi_outputs():
    try:
        return list(mido.get_output_names())
    except Exception:
        return []


def list_midi_inputs():
    try:
        return list(mido.get_input_names())
    except Exception:
        return []


def pick_mpk_port(names):
    return next((n for n in names if is_mpk_name(n)), None)

PRESET_MW = "mw_cc"
PRESET_KEY = "key_xpose"
PRESET_PAD = "pad_xpose"
PRESET_PTR = "pointer"
PRESET_KNOB = "knob_banks"
PRESET_CHORD = "chords"
PRESET_CLIP = "clips"
PRESET_PB = "pb_pass"
PRESET_KEY_CH = "key_ch"
PRESET_PAD_CH = "pad_ch"

JOY_CHOICES = (
    (PRESET_MW, "MW/PB + Custom CCs"),
    (PRESET_KEY, "Key Transpose"),
    (PRESET_PAD, "Pad Transpose"),
    (PRESET_KEY_CH, "Key Channel"),
    (PRESET_PAD_CH, "Pad Channel"),
    (PRESET_PTR, "D-Pad / Mouse"),
    (PRESET_PB, "Pitchbend pass"),
)
PAD_CHOICES = (
    (PRESET_MW, "Custom CCs"),
    (PRESET_KEY, "Key Channel"),
    (PRESET_PAD, "Pad Channel"),
    (PRESET_PTR, "Keystrokes & Clicks"),
    (PRESET_KNOB, "Knob Banks"),
    (PRESET_CHORD, "Chord Macros"),
    (PRESET_CLIP, "Clip Macros"),
)
JOY_LABELS = {k: v for k, v in JOY_CHOICES}
PAD_LABELS = {k: v for k, v in PAD_CHOICES}
JOY_BY_LABEL = {v: k for k, v in JOY_CHOICES}
PAD_BY_LABEL = {v: k for k, v in PAD_CHOICES}
DEFAULT_JOY = (PRESET_MW, PRESET_KEY, PRESET_PAD, PRESET_PTR)
DEFAULT_PAD = (PRESET_MW, PRESET_KEY, PRESET_PAD, PRESET_PTR)


class ProgConfig:
    """One MPK PROG: joystick channel n + pad CC channel n+9."""

    def __init__(self, joy_preset, pad_preset):
        self.joy_preset = joy_preset
        self.pad_preset = pad_preset
        self.cc_a = 30
        self.cc_b = 31
        self.cc_map = list(range(16))
        self.pointer_mode = "mouse"  # "mouse" | "dpad"
        self.mouse_sens = 8.0
        self.cc13_map = [[] for _ in range(16)]
        self.chord_map = [[] for _ in range(16)]
        self.chord_delay = [True] * 16  # replay learned timing when True
        self.chord_xpose = [0] * 16     # per-slot semitone offset
        self.chord_ch = [1] * 16        # local output channel
        self.chord_ch_global = [True] * 16
        self.cc_ch_global = True
        self.cc_ch = 10
        self.clip_map = [[] for _ in range(16)]
        self.clip_delay = [True] * 16
        self.clip_xpose = [0] * 16
        self.clip_mode = ["continuous"] * 16  # "continuous" | "one-shot"


# --------------------------
# Shared mapper state
# --------------------------
class MapperState:
    def __init__(self):
        self.lock = threading.Lock()
        self.gk = 0          # key transpose (semitones)
        self.pk = 0          # pad transpose
        self.gc = 1          # key / sustain / pitch / program output channel (1-16)
        self.gd = 10         # pad output channel (1-16)
        self.blink_high = False
        self.current_program = 0
        self.progs = [ProgConfig(j, p) for j, p in zip(DEFAULT_JOY, DEFAULT_PAD)]
        self.pointer_prog = 3  # last PROG that drove the pointer
        # Pointer axes in -1..1, written by MIDI thread, read by pointer thread
        self.axis_x = 0.0
        self.axis_y = 0.0
        # Pad LED display: "key" shows Key Channel, "pad" shows Pad Channel
        self.led_mode = "key"
        self.chord_learn = None  # (prog, slot) while a chord/clip slot is latch-learning
        self.clip_overdub = [False] * 4
        # 16 nameable knob banks for CC20–27. Bank n (1-16) defaults to CCs
        # (n-1)*8 .. (n-1)*8+7 so the 16 banks cover CC 0–127.
        self.knob_bank = 1
        self.knob_bank_names = [f"Bank {i + 1}" for i in range(16)]
        self.knob_ccs = [[b * 8 + k for k in range(8)] for b in range(16)]
        self.knob_ch_global = [True] * 16
        self.knob_ch = [[1] * 8 for _ in range(16)]


def clamp(n, lo, hi):
    return lo if n < lo else hi if n > hi else n


def normalize_knob_ch(raw):
    """16 banks × 8 knobs. Accepts legacy per-bank scalars."""
    if not raw:
        return [[1] * 8 for _ in range(16)]
    first = raw[0]
    if isinstance(first, (list, tuple)):
        out = []
        for row in raw[:16]:
            vals = []
            for x in list(row)[:8]:
                try:
                    vals.append(clamp(int(x), 1, 16))
                except (TypeError, ValueError):
                    vals.append(1)
            while len(vals) < 8:
                vals.append(vals[-1] if vals else 1)
            out.append(vals)
        while len(out) < 16:
            out.append([1] * 8)
        return out
    out = []
    for v in list(raw)[:16]:
        try:
            ch = clamp(int(v), 1, 16)
        except (TypeError, ValueError):
            ch = 1
        out.append([ch] * 8)
    while len(out) < 16:
        out.append([1] * 8)
    return out


def ensure_mapper_state(s=None):
    """Fill fields added after earlier builds so a stale MapperState still runs."""
    s = state if s is None else s
    if not getattr(s, "knob_bank_names", None) or len(s.knob_bank_names) != 16:
        s.knob_bank_names = [f"Bank {i + 1}" for i in range(16)]
    if not getattr(s, "knob_ccs", None) or len(s.knob_ccs) != 16:
        s.knob_ccs = [[b * 8 + k for k in range(8)] for b in range(16)]
    if not getattr(s, "knob_ch_global", None) or len(s.knob_ch_global) != 16:
        s.knob_ch_global = [True] * 16
    s.knob_ch = normalize_knob_ch(getattr(s, "knob_ch", None))
    if not hasattr(s, "knob_bank"):
        s.knob_bank = 1
    if not hasattr(s, "chord_learn"):
        s.chord_learn = None
    if not getattr(s, "clip_overdub", None) or len(s.clip_overdub) != 4:
        s.clip_overdub = [False] * 4
    defaults = list(zip(DEFAULT_JOY, DEFAULT_PAD))
    for i, cfg in enumerate(getattr(s, "progs", []) or []):
        joy, pad = defaults[i] if i < 4 else (PRESET_MW, PRESET_MW)
        if not hasattr(cfg, "joy_preset"):
            cfg.joy_preset = getattr(cfg, "preset", joy)
        if not hasattr(cfg, "pad_preset"):
            cfg.pad_preset = getattr(cfg, "preset", pad)
        if not getattr(cfg, "chord_ch", None) or len(cfg.chord_ch) != 16:
            cfg.chord_ch = [1] * 16
        if not getattr(cfg, "chord_ch_global", None) or len(cfg.chord_ch_global) != 16:
            cfg.chord_ch_global = [True] * 16
        if not hasattr(cfg, "cc_ch_global"):
            cfg.cc_ch_global = True
        if not hasattr(cfg, "cc_ch"):
            cfg.cc_ch = 10
        if not getattr(cfg, "chord_delay", None) or len(cfg.chord_delay) != 16:
            cfg.chord_delay = [True] * 16
        if not getattr(cfg, "chord_xpose", None) or len(cfg.chord_xpose) != 16:
            cfg.chord_xpose = [0] * 16
        if not getattr(cfg, "chord_map", None) or len(cfg.chord_map) != 16:
            cfg.chord_map = [[] for _ in range(16)]
        if not getattr(cfg, "clip_map", None) or len(cfg.clip_map) != 16:
            cfg.clip_map = [[] for _ in range(16)]
        if not getattr(cfg, "clip_delay", None) or len(cfg.clip_delay) != 16:
            cfg.clip_delay = [True] * 16
        if not getattr(cfg, "clip_xpose", None) or len(cfg.clip_xpose) != 16:
            cfg.clip_xpose = [0] * 16
        if not getattr(cfg, "clip_mode", None) or len(cfg.clip_mode) != 16:
            cfg.clip_mode = ["continuous"] * 16
    return s


state = MapperState()
ensure_mapper_state(state)
stop_event = threading.Event()
# (action_name, down: bool) — MIDI thread produces, Tk thread consumes
input_events = queue.Queue()

JOY_CC_A = 30
JOY_CC_B = 31
JOY_CC_Y = 1      # MPK Mini joystick vertical (consumed on ch4, never forwarded)
DEADZONE = 0.10
TRANSPOSE_MIN, TRANSPOSE_MAX = -48, 48
PAD_CH_LO, PAD_CH_HI = 9, 12   # MIDI channels 10-13 (0-indexed)
PAD_NOTE_BASE = 60             # pad 1 = C4 in our sysex; slots 0–15 = notes 60–75
DPAD_THRESHOLD = 0.45
CHORD_LEARN_SETTLE = 0.30      # seconds after last key (all up) before learn commits
CHORD_LEARN_TAP_DEBOUNCE = 0.08
KNOB_LEARN_GUARD = 0.30          # ignore Learn while knobs (CC20–27 ch1–4) are noisy

# Akai MPK Mini MK2 SysEx (mido data = bytes between F0 and F7)
#   0x66 dump request   0x67 dump reply   0x64 dump write
# Payload after 47 00 26 CMD 00 6D:
#   PROG 1–4, pad MIDI ch 0-indexed (9–12), key MIDI ch 0-indexed (0–3)
_SYSEX_HDR = (0x47, 0x00, 0x26)
_SYSEX_DUMP_PROG1 = (
    0x47, 0x00, 0x26, 0x67, 0x00, 0x6D, 0x01, 0x09, 0x00, 0x04, 0x00, 0x03, 0x04, 0x00,
    0x01, 0x00, 0x03, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x1E, 0x1F, 0x3C, 0x00, 0x00,
    0x00, 0x3D, 0x01, 0x01, 0x00, 0x3E, 0x02, 0x02, 0x00, 0x3F, 0x03, 0x03, 0x00, 0x40, 0x04,
    0x04, 0x00, 0x41, 0x05, 0x05, 0x00, 0x42, 0x06, 0x06, 0x00, 0x43, 0x07, 0x07, 0x00, 0x44,
    0x08, 0x08, 0x00, 0x45, 0x09, 0x09, 0x00, 0x46, 0x0A, 0x0A, 0x00, 0x47, 0x0B, 0x0B, 0x00,
    0x48, 0x0C, 0x0C, 0x00, 0x49, 0x0D, 0x0D, 0x00, 0x4A, 0x0E, 0x0E, 0x00, 0x4B, 0x0F, 0x0F,
    0x00, 0x14, 0x00, 0x7F, 0x15, 0x00, 0x7F, 0x16, 0x00, 0x7F, 0x17, 0x00, 0x7F, 0x18, 0x00,
    0x7F, 0x19, 0x00, 0x7F, 0x1A, 0x00, 0x7F, 0x1B, 0x00, 0x7F, 0x0C,
)


def _sysex_expected_dump(prog):
    data = list(_SYSEX_DUMP_PROG1)
    data[6] = prog
    data[7] = 8 + prog          # pad ch 10–13 (0-indexed 9–12)
    data[8] = prog - 1          # key/joy ch 1–4 (0-indexed 0–3)
    return data


def _sysex_write(prog):
    data = _sysex_expected_dump(prog)
    data[3] = 0x64
    return data


def _sysex_request(prog):
    return [0x47, 0x00, 0x26, 0x66, 0x00, 0x01, prog]


def _sysex_dump_ok(data, prog):
    return list(data) == _sysex_expected_dump(prog)


def clamp_note(n):
    return clamp(int(n), 0, 127)


_NOTE_NAMES = ("C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B")


def format_note(n):
    n = clamp_note(n)
    return f"{_NOTE_NAMES[n % 12]}{n // 12 - 1}"


def format_chord(notes, xpose=0):
    events = parse_chord(notes)
    if not events:
        return "(none)"
    xpose = int(xpose or 0)
    parts = []
    for ev in events:
        name = format_note(ev["note"] + xpose)
        ms = int(round(ev["delay"] * 1000.0))
        parts.append(name if ms <= 0 else f"{name}+{ms}")
    shown = " ".join(parts)
    return shown


def parse_chord(notes):
    """List of {note, delay, vel} in play order. delay is seconds from the first note."""
    out, seen = [], []
    for item in notes or []:
        delay, vel = 0.0, 100
        try:
            if isinstance(item, dict):
                n = clamp_note(item.get("note", item.get("n", 0)))
                delay = max(0.0, float(item.get("delay", 0.0) or 0.0))
                vel = clamp(int(item.get("vel", 100) or 100), 1, 127)
            elif isinstance(item, (list, tuple)) and item:
                n = clamp_note(item[0])
                if len(item) > 1:
                    delay = max(0.0, float(item[1] or 0.0))
                if len(item) > 2:
                    vel = clamp(int(item[2] or 100), 1, 127)
            else:
                n = clamp_note(item)
        except (TypeError, ValueError):
            continue
        if n in seen:
            continue
        seen.append(n)
        out.append({"note": n, "delay": delay, "vel": vel})
    return out


def parse_clip(notes):
    """Multi-channel clip events: {note, delay, vel, ch, duration}."""
    out = []
    for item in notes or []:
        delay, vel, ch, dur = 0.0, 100, 1, 0.25
        try:
            if isinstance(item, dict):
                n = clamp_note(item.get("note", item.get("n", 0)))
                delay = max(0.0, float(item.get("delay", 0.0) or 0.0))
                vel = clamp(int(item.get("vel", 100) or 100), 1, 127)
                ch = clamp(int(item.get("ch", item.get("channel", 1)) or 1), 1, 16)
                dur = max(0.02, float(item.get("duration", 0.25) or 0.25))
            elif isinstance(item, (list, tuple)) and item:
                n = clamp_note(item[0])
                if len(item) > 1:
                    delay = max(0.0, float(item[1] or 0.0))
                if len(item) > 2:
                    vel = clamp(int(item[2] or 100), 1, 127)
                if len(item) > 3:
                    ch = clamp(int(item[3] or 1), 1, 16)
                if len(item) > 4:
                    dur = max(0.02, float(item[4] or 0.25))
            else:
                n = clamp_note(item)
        except (TypeError, ValueError):
            continue
        out.append({"note": n, "delay": delay, "vel": vel, "ch": ch, "duration": dur})
    out.sort(key=lambda e: (e["delay"], e["ch"], e["note"]))
    return out


def format_clip(notes, xpose=0):
    events = parse_clip(notes)
    if not events:
        return "(none)"
    xpose = int(xpose or 0)
    parts = []
    for ev in events:
        name = format_note(ev["note"] + xpose)
        ch = int(ev.get("ch", 1))
        label = f"{name}:{ch}"
        ms = int(round(ev["delay"] * 1000.0))
        parts.append(label if ms <= 0 else f"{label}+{ms}")
    return " ".join(parts)


def merge_clip_events(base, extra):
    return parse_clip(list(base or []) + list(extra or []))


def serialize_chord_patch(name, slots, delays, xposes=None, chs=None, globs=None,
                         ccs=None, srcs=None):
    lines = ["MiniMapper chord patch v1", f"name: {name or 'Patch'}"]
    xposes = list(xposes or [0] * 16)
    chs = list(chs or [1] * 16)
    globs = list(globs or [True] * 16)
    ccs = list(ccs or [0] * 16)
    srcs = list(srcs or ["pad"] * 16)
    for i, notes in enumerate(slots):
        events = parse_chord(notes)
        if not events:
            continue
        on = "on" if delays[i] else "off"
        xp = int(xposes[i] if i < len(xposes) else 0)
        ch = int(chs[i] if i < len(chs) else 1)
        gl = "global" if (globs[i] if i < len(globs) else True) else "local"
        cc = int(ccs[i] if i < len(ccs) else 0)
        src = srcs[i] if i < len(srcs) else "pad"
        lines.append(
            f"slot: {i} delay: {on} xpose: {xp} ch: {ch} route: {gl} cc: {cc} src: {src}"
        )
        for ev in events:
            ms = int(round(ev["delay"] * 1000.0))
            lines.append(f"note: {ev['note']} delay_ms: {ms} vel: {ev['vel']}")
    lines.append("")
    return "\n".join(lines)


def parse_chord_patch(text):
    name = "Patch"
    slots = [[] for _ in range(16)]
    delays = [True] * 16
    xposes = [0] * 16
    chs = [1] * 16
    globs = [True] * 16
    ccs = [0] * 16
    srcs = ["pad"] * 16
    cur = None
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        low = line.lower()
        if low.startswith("name:"):
            name = line.split(":", 1)[1].strip() or name
            continue
        if low.startswith("slot:"):
            parts = line.replace(",", " ").split()
            idx, delay_on, xp, ch, gl, cc, src = 0, True, 0, 1, True, 0, "pad"
            for i, tok in enumerate(parts):
                key = tok.lower().rstrip(":")
                nxt = parts[i + 1] if i + 1 < len(parts) else ""
                if key == "slot":
                    try:
                        idx = clamp(int(nxt), 0, 15)
                    except ValueError:
                        pass
                elif key == "delay":
                    delay_on = nxt.lower() not in ("off", "0", "false", "no")
                elif key in ("xpose", "transpose"):
                    try:
                        xp = clamp(int(nxt), TRANSPOSE_MIN, TRANSPOSE_MAX)
                    except ValueError:
                        pass
                elif key in ("ch", "channel"):
                    try:
                        ch = clamp(int(nxt), 1, 16)
                    except ValueError:
                        pass
                elif key == "route":
                    gl = nxt.lower() not in ("local", "off", "0")
                elif key == "cc":
                    try:
                        cc = clamp(int(nxt), 0, 127)
                    except ValueError:
                        pass
                elif key == "src":
                    src = "knob" if nxt.lower().startswith("knob") else "pad"
            cur = idx
            delays[idx] = delay_on
            xposes[idx] = xp
            chs[idx] = ch
            globs[idx] = gl
            ccs[idx] = cc
            srcs[idx] = src
            slots[idx] = []
            continue
        if low.startswith("note:") and cur is not None:
            parts = line.replace(",", " ").split()
            n, ms, vel = 60, 0, 100
            for i, tok in enumerate(parts):
                key = tok.lower().rstrip(":")
                nxt = parts[i + 1] if i + 1 < len(parts) else ""
                try:
                    if key == "note":
                        n = clamp_note(int(nxt))
                    elif key in ("delay_ms", "ms"):
                        ms = max(0, int(float(nxt)))
                    elif key in ("vel", "velocity"):
                        vel = clamp(int(nxt), 1, 127)
                except ValueError:
                    pass
            slots[cur].append({"note": n, "delay": ms / 1000.0, "vel": vel})
    return name, slots, delays, xposes, chs, globs, ccs, srcs


def write_chord_midi(path, events, use_delay=True, name=""):
    """One-track SMF: note-ons in learned order/timing, then note-offs."""
    events = parse_chord(events)
    if not events:
        return False
    mid = mido.MidiFile(ticks_per_beat=1000)
    track = mido.MidiTrack()
    mid.tracks.append(track)
    track.append(mido.MetaMessage("set_tempo", tempo=1_000_000))  # 1 tick = 1 ms
    if name:
        track.append(mido.MetaMessage("track_name", name=str(name)[:32]))
    t_prev = 0.0
    for ev in events:
        t = float(ev["delay"]) if use_delay else 0.0
        dt = max(0, int(round((t - t_prev) * 1000.0)))
        track.append(mido.Message(
            "note_on", note=ev["note"], velocity=ev["vel"], time=dt, channel=0,
        ))
        t_prev = t
    hold_ms = 500
    first = True
    for ev in events:
        track.append(mido.Message(
            "note_off", note=ev["note"], velocity=0,
            time=hold_ms if first else 0, channel=0,
        ))
        first = False
    mid.save(path)
    return True


def write_chord_midi_sequence(path, chords, name=""):
    """One SMF: filled chords in slot order, each occupying half a bar at 120 BPM."""
    ticks_per_beat = 480
    half_bar = ticks_per_beat * 2  # 2 beats = half a 4/4 bar
    mid = mido.MidiFile(ticks_per_beat=ticks_per_beat)
    track = mido.MidiTrack()
    mid.tracks.append(track)
    track.append(mido.MetaMessage("set_tempo", tempo=500000))  # 120 BPM
    if name:
        track.append(mido.MetaMessage("track_name", name=str(name)[:32]))
    abs_events = []  # (tick, 'note_on'|'note_off', note, vel)
    t0 = 0
    for events, use_delay, xpose in chords:
        events = parse_chord(events)
        if not events:
            continue
        for ev in events:
            delay_s = float(ev["delay"]) if use_delay else 0.0
            on_tick = t0 + int(round(delay_s * ticks_per_beat * 2))  # 1s = half bar
            on_tick = min(on_tick, t0 + half_bar - 1)
            note = clamp_note(ev["note"] + int(xpose or 0))
            abs_events.append((on_tick, "note_on", note, ev["vel"]))
            abs_events.append((t0 + half_bar, "note_off", note, 0))
        t0 += half_bar
    if not abs_events:
        return False
    abs_events.sort(key=lambda x: (x[0], 0 if x[1] == "note_off" else 1))
    prev = 0
    for tick, kind, note, vel in abs_events:
        track.append(mido.Message(kind, note=note, velocity=vel,
                                  time=max(0, tick - prev), channel=0))
        prev = tick
    mid.save(path)
    return True


def pad_note_to_slot(note):
    """Map an incoming pad note to chord slot 0–15, or None."""
    n = int(note)
    if PAD_NOTE_BASE <= n <= PAD_NOTE_BASE + 15:
        return n - PAD_NOTE_BASE
    if 36 <= n <= 51:
        return n - 36
    if 0 <= n <= 15:
        return n
    return None


def wrap_channel(ch, inc):
    ch = ch + (1 if inc else -1)
    if ch > 16:
        return 1
    if ch < 1:
        return 16
    return ch


_MOD_ORDER = ("ctrl", "alt", "shift", "cmd")
_MOD_ACTIONS = frozenset(_MOD_ORDER)

# CGEvent flag bits (kCGEventFlagMask* | NX_DEVICELxxxKEYMASK)
_MAC_MOD_FLAGS = {
    "shift": 0x00020000 | 0x00000002,
    "ctrl":  0x00040000 | 0x00000001,
    "alt":   0x00080000 | 0x00000020,
    "cmd":   0x00100000 | 0x00000008,
}


def combo_mod_flags(combo):
    flags = 0
    for action in combo:
        flags |= _MAC_MOD_FLAGS.get(action, 0)
    return flags

_TK_KEYMAP = {
    "shift_l": "shift", "shift_r": "shift",
    "control_l": "ctrl", "control_r": "ctrl",
    "alt_l": "alt", "alt_r": "alt",
    "option_l": "alt", "option_r": "alt",
    "meta_l": "cmd", "meta_r": "cmd", "command": "cmd",
    "super_l": "cmd", "super_r": "cmd", "win_l": "cmd", "win_r": "cmd",
    "return": "enter", "kp_enter": "enter",
    "escape": "esc",
    "space": "space",
    "tab": "tab",
    "backspace": "backspace",
    "delete": "delete", "del": "delete",
    "up": "arrow up", "down": "arrow down",
    "left": "arrow left", "right": "arrow right",
}
_TK_KEYMAP.update({f"f{i}": f"f{i}" for i in range(1, 13)})
_TK_KEYMAP.update({ch: ch for ch in "abcdefghijklmnopqrstuvwxyz"})
_TK_KEYMAP.update({ch: ch for ch in "0123456789"})


def tk_event_to_action(event):
    keysym = (event.keysym or "").lower()
    return _TK_KEYMAP.get(keysym)


def normalize_combo(keys):
    seen = []
    for k in keys:
        if k and k != "none" and k not in seen:
            seen.append(k)
    mods = [m for m in _MOD_ORDER if m in seen]
    rest = [k for k in seen if k not in _MOD_ORDER]
    return mods + rest


def format_combo(combo):
    combo = combo or []
    return "+".join(combo) if combo else "(none)"


def parse_combo(value):
    """Accept a list, or a legacy single-action string."""
    if not value or value == "none":
        return []
    if isinstance(value, (list, tuple)):
        return normalize_combo(list(value))
    if isinstance(value, str):
        parts = [p.strip() for p in value.split("+") if p.strip() and p.strip() != "none"]
        return normalize_combo(parts)
    return []


def is_hold_mapping(combo):
    """Single key or mouse click uses pad hold (CC>0 down, 0 up).
    Combos and explicit double-clicks tap on CC>0 only."""
    return len(combo) == 1 and combo[0] not in _MOUSE_DOUBLE

# macOS virtual key codes (ANSI US)
_MAC_KEY = {
    "a": 0x00, "s": 0x01, "d": 0x02, "f": 0x03, "h": 0x04, "g": 0x05,
    "z": 0x06, "x": 0x07, "c": 0x08, "v": 0x09, "b": 0x0B, "q": 0x0C,
    "w": 0x0D, "e": 0x0E, "r": 0x0F, "y": 0x10, "t": 0x11, "1": 0x12,
    "2": 0x13, "3": 0x14, "4": 0x15, "6": 0x16, "5": 0x17, "9": 0x19,
    "7": 0x1A, "8": 0x1C, "0": 0x1D, "o": 0x1F, "u": 0x20, "i": 0x22,
    "p": 0x23, "enter": 0x24, "l": 0x25, "j": 0x26, "k": 0x28, "n": 0x2D,
    "m": 0x2E, "tab": 0x30, "space": 0x31, "backspace": 0x33, "esc": 0x35,
    "cmd": 0x37, "shift": 0x38, "alt": 0x3A, "ctrl": 0x3B,
    "f5": 0x60, "f6": 0x61, "f7": 0x62, "f3": 0x63, "f8": 0x64, "f9": 0x65,
    "f11": 0x67, "f10": 0x6D, "f12": 0x6F, "delete": 0x75, "f4": 0x76,
    "f2": 0x78, "f1": 0x7A,
    "arrow left": 0x7B, "arrow right": 0x7C, "arrow down": 0x7D, "arrow up": 0x7E,
}

# Windows virtual-key codes
_WIN_VK = {
    "backspace": 0x08, "tab": 0x09, "enter": 0x0D, "shift": 0x10,
    "ctrl": 0x11, "alt": 0x12, "esc": 0x1B, "space": 0x20,
    "page up": 0x21, "page down": 0x22, "end": 0x23, "home": 0x24,
    "arrow left": 0x25, "arrow up": 0x26, "arrow right": 0x27, "arrow down": 0x28,
    "insert": 0x2D, "delete": 0x2E,
    "cmd": 0x5B,  # Left Windows key
    ";": 0xBA, "=": 0xBB, ",": 0xBC, "-": 0xBD, ".": 0xBE, "/": 0xBF,
    "`": 0xC0, "[": 0xDB, "\\": 0xDC, "]": 0xDD, "'": 0xDE,
}
_WIN_VK.update({chr(c): c for c in range(ord("A"), ord("Z") + 1)})
_WIN_VK.update({chr(c): c for c in range(ord("0"), ord("9") + 1)})
_WIN_VK.update({f"f{i}": 0x70 + i - 1 for i in range(1, 13)})
_WIN_VK.update({chr(c): ord(chr(c).upper()) for c in range(ord("a"), ord("z") + 1)})
_WIN_VK_EXTENDED = frozenset({
    0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  # pgup..arrows
    0x2D, 0x2E,  # insert, delete
    0x5B, 0x5C,  # win
})

_MOUSE_BUTTONS = ("mouse left", "mouse right", "mouse middle")
_MOUSE_DOUBLE = {
    "mouse left double": "mouse left",
    "mouse right double": "mouse right",
    "mouse middle double": "mouse middle",
}


def _win_input_types():
    """SendInput structs. Built lazily so Mac never imports wintypes."""
    from ctypes import wintypes

    class MOUSEINPUT(ctypes.Structure):
        _fields_ = (
            ("dx", wintypes.LONG),
            ("dy", wintypes.LONG),
            ("mouseData", wintypes.DWORD),
            ("dwFlags", wintypes.DWORD),
            ("time", wintypes.DWORD),
            ("dwExtraInfo", ctypes.c_void_p),
        )

    class KEYBDINPUT(ctypes.Structure):
        _fields_ = (
            ("wVk", wintypes.WORD),
            ("wScan", wintypes.WORD),
            ("dwFlags", wintypes.DWORD),
            ("time", wintypes.DWORD),
            ("dwExtraInfo", ctypes.c_void_p),
        )

    class HARDWAREINPUT(ctypes.Structure):
        _fields_ = (
            ("uMsg", wintypes.DWORD),
            ("wParamL", wintypes.WORD),
            ("wParamH", wintypes.WORD),
        )

    class INPUT(ctypes.Structure):
        class _I(ctypes.Union):
            _fields_ = (("mi", MOUSEINPUT), ("ki", KEYBDINPUT), ("hi", HARDWAREINPUT))
        _anonymous_ = ("i",)
        _fields_ = (("type", wintypes.DWORD), ("i", _I))

    return INPUT, MOUSEINPUT, KEYBDINPUT


# --------------------------
# Pointer (mouse) backend — Tk thread only
# --------------------------
class _CGPoint(ctypes.Structure):
    _fields_ = [("x", ctypes.c_double), ("y", ctypes.c_double)]


class PointerDriver:
    """Relative cursor move via real mouse-moved / mouse-dragged events
    (warp alone never delivers click-and-drag to apps)."""

    _CG_MOUSE_MOVED = 5
    _CG_LEFT_DRAGGED = 6
    _CG_RIGHT_DRAGGED = 7
    _CG_OTHER_DRAGGED = 27
    _CG_HID_TAP = 0
    _CG_DELTA_X = 4  # kCGMouseEventDeltaX
    _CG_DELTA_Y = 5

    def __init__(self):
        self._move_fn = None
        self._read_pos = None
        self._tracked = None
        self._error = None
        if IS_MAC:
            self._try_mac_warp()
        elif IS_WIN:
            self._try_win()

    def available(self):
        return self._move_fn is not None

    def position(self):
        """Current cursor in screen pixels, or None."""
        if self._read_pos is not None:
            try:
                pos = self._read_pos()
            except Exception:
                pos = None
            if pos is not None:
                if self._tracked is not None:
                    self._tracked["x"], self._tracked["y"] = pos
                return pos
        if self._tracked is not None:
            return self._tracked["x"], self._tracked["y"]
        return None

    def move(self, dx, dy, drag=None):
        if not dx and not dy:
            return
        if self._move_fn is None:
            return
        try:
            self._move_fn(int(dx), int(dy), drag)
        except TypeError:
            self._move_fn(int(dx), int(dy))
        except Exception as exc:
            self._error = str(exc)

    def _try_mac_warp(self):
        """CGWarpMouseCursorPosition + HIGetMousePosition (out-pointer). No CFRelease."""
        try:
            cg = ctypes.CDLL(
                "/System/Library/Frameworks/CoreGraphics.framework/CoreGraphics"
            )
            warp = cg.CGWarpMouseCursorPosition
            warp.argtypes = [_CGPoint]
            warp.restype = ctypes.c_int32

            assoc = cg.CGAssociateMouseAndMouseCursorPosition
            assoc.argtypes = [ctypes.c_bool]
            assoc.restype = ctypes.c_int32

            get_pos = None
            for libpath in (
                "/System/Library/Frameworks/Carbon.framework/Frameworks/HIToolbox.framework/HIToolbox",
                "/System/Library/Frameworks/Carbon.framework/Carbon",
            ):
                try:
                    hi = ctypes.CDLL(libpath)
                    fn = hi.HIGetMousePosition
                    fn.argtypes = [ctypes.c_uint32, ctypes.c_void_p, ctypes.POINTER(_CGPoint)]
                    fn.restype = ctypes.c_int32
                    get_pos = fn
                    break
                except (OSError, AttributeError):
                    continue

            pixels_w = cg.CGDisplayPixelsWide
            pixels_w.argtypes = [ctypes.c_uint32]
            pixels_w.restype = ctypes.c_size_t
            pixels_h = cg.CGDisplayPixelsHigh
            pixels_h.argtypes = [ctypes.c_uint32]
            pixels_h.restype = ctypes.c_size_t
            main_id = cg.CGMainDisplayID
            main_id.argtypes = []
            main_id.restype = ctypes.c_uint32

            tracked = {"x": float(pixels_w(main_id()) or 800) / 2.0,
                       "y": float(pixels_h(main_id()) or 600) / 2.0}

            k_screen_pixel = 2  # kHICoordSpaceScreenPixel

            def _read():
                if get_pos is None:
                    return None
                pt = _CGPoint()
                if get_pos(k_screen_pixel, None, ctypes.byref(pt)) == 0:
                    return pt.x, pt.y
                return None

            create_mouse = getattr(cg, "CGEventCreateMouseEvent", None)
            post = getattr(cg, "CGEventPost", None)
            set_int = getattr(cg, "CGEventSetIntegerValueField", None)
            create_source = getattr(cg, "CGEventSourceCreate", None)
            source = None
            if create_mouse is not None:
                create_mouse.argtypes = [
                    ctypes.c_void_p, ctypes.c_uint32, _CGPoint, ctypes.c_uint32,
                ]
                create_mouse.restype = ctypes.c_void_p
            if post is not None:
                post.argtypes = [ctypes.c_uint32, ctypes.c_void_p]
                post.restype = None
            if set_int is not None:
                set_int.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int64]
                set_int.restype = None
            if create_source is not None:
                create_source.argtypes = [ctypes.c_int32]
                create_source.restype = ctypes.c_void_p
                source = create_source(1)  # kCGEventSourceStateHIDSystemState

            def _mac_move(dx, dy, drag=None):
                pos = _read()
                if pos is not None:
                    tracked["x"], tracked["y"] = pos
                tracked["x"] += dx
                tracked["y"] += dy
                pt = _CGPoint(tracked["x"], tracked["y"])
                posted = False
                if create_mouse is not None and post is not None and source:
                    if drag == "mouse left":
                        etype, btn = self._CG_LEFT_DRAGGED, 0
                    elif drag == "mouse right":
                        etype, btn = self._CG_RIGHT_DRAGGED, 1
                    elif drag == "mouse middle":
                        etype, btn = self._CG_OTHER_DRAGGED, 2
                    else:
                        etype, btn = self._CG_MOUSE_MOVED, 0
                    ev = create_mouse(source, etype, pt, btn)
                    if ev:
                        if set_int is not None:
                            set_int(ev, self._CG_DELTA_X, int(dx))
                            set_int(ev, self._CG_DELTA_Y, int(dy))
                        post(self._CG_HID_TAP, ev)
                        posted = True
                if not posted:
                    warp(pt)
                    assoc(True)

            self._move_fn = _mac_move
            self._read_pos = _read
            self._tracked = tracked
        except Exception as exc:
            self._error = str(exc)
            self._move_fn = None

    def _try_win(self):
        try:
            from ctypes import wintypes
            INPUT, MOUSEINPUT, _KEYBDINPUT = _win_input_types()
            user32 = ctypes.windll.user32
            try:
                user32.SetProcessDPIAware()
            except Exception:
                pass
            pt = wintypes.POINT()
            SM_XVIRTUALSCREEN, SM_YVIRTUALSCREEN = 76, 77
            SM_CXVIRTUALSCREEN, SM_CYVIRTUALSCREEN = 78, 79
            MOUSEEVENTF_MOVE = 0x0001
            MOUSEEVENTF_ABSOLUTE = 0x8000
            MOUSEEVENTF_VIRTUALDESK = 0x4000
            INPUT_MOUSE = 0

            def _norm(x, y):
                vx = user32.GetSystemMetrics(SM_XVIRTUALSCREEN)
                vy = user32.GetSystemMetrics(SM_YVIRTUALSCREEN)
                vw = max(1, user32.GetSystemMetrics(SM_CXVIRTUALSCREEN) - 1)
                vh = max(1, user32.GetSystemMetrics(SM_CYVIRTUALSCREEN) - 1)
                ax = int((int(x) - vx) * 65535 / vw)
                ay = int((int(y) - vy) * 65535 / vh)
                return ax, ay

            def _win_pos():
                user32.GetCursorPos(ctypes.byref(pt))
                return float(pt.x), float(pt.y)

            def _win_move(dx, dy, drag=None):
                user32.GetCursorPos(ctypes.byref(pt))
                ax, ay = _norm(pt.x + int(dx), pt.y + int(dy))
                inp = INPUT()
                inp.type = INPUT_MOUSE
                inp.mi = MOUSEINPUT(
                    ax, ay, 0,
                    MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE | MOUSEEVENTF_VIRTUALDESK,
                    0, None,
                )
                user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))

            self._move_fn = _win_move
            self._read_pos = _win_pos
            self._tracked = {"x": 0.0, "y": 0.0}
        except Exception as exc:
            self._error = str(exc)
            self._move_fn = None


# --------------------------
# Keystrokes / mouse clicks — Tk thread only
# --------------------------
class InputDriver:
    """Keystrokes + mouse buttons, posted from the Tk thread.

    Mouse clicks never go through pynput: its macOS location read returns
    (0,0), which teleports the click to the top-left. Clicks use the same
    HIGetMousePosition / GetCursorPos path as the analog joystick.
    """

    _CG_LEFT_DOWN, _CG_LEFT_UP = 1, 2
    _CG_RIGHT_DOWN, _CG_RIGHT_UP = 3, 4
    _CG_OTHER_DOWN, _CG_OTHER_UP = 25, 26
    _CG_BTN_LEFT, _CG_BTN_RIGHT, _CG_BTN_CENTER = 0, 1, 2
    _CG_HID_TAP = 0
    _CG_SESSION_TAP = 1
    _CG_SRC_HID_STATE = 1
    _CG_CLICK_STATE_FIELD = 1  # kCGMouseEventClickState

    _WIN_MOUSE = {
        ("mouse left", True): 0x0002,
        ("mouse left", False): 0x0004,
        ("mouse right", True): 0x0008,
        ("mouse right", False): 0x0010,
        ("mouse middle", True): 0x0020,
        ("mouse middle", False): 0x0040,
    }

    def __init__(self, pointer=None):
        self.pointer = pointer
        self._key_fn = None
        self._mouse_fn = None
        self._error = None
        self._held = set()
        self._click_rec = {}       # action -> {t, n, pos}
        self._click_up = {}        # action -> click count for matching up
        self._dbl_interval = 0.5
        if IS_WIN:
            try:
                ms = ctypes.windll.user32.GetDoubleClickTime()
                if ms:
                    self._dbl_interval = max(0.2, ms / 1000.0)
            except Exception:
                pass
        if IS_MAC:
            self._try_mac()
        elif IS_WIN:
            self._try_win()

    def available(self):
        return self._key_fn is not None or self._mouse_fn is not None

    def held_mouse(self):
        for b in _MOUSE_BUTTONS:
            if b in self._held:
                return b
        return None

    def _next_click_count(self, action, pos, forced=None):
        if forced:
            self._click_up[action] = forced
            return forced
        now = time.monotonic()
        rec = self._click_rec.get(action)
        count = 1
        if rec is not None and (now - rec["t"]) <= self._dbl_interval:
            px, py = rec["pos"]
            if pos is None or ((pos[0] - px) ** 2 + (pos[1] - py) ** 2) <= 256:
                count = rec["n"] + 1
                if count > 3:
                    count = 1
        self._click_rec[action] = {
            "t": now,
            "n": count,
            "pos": pos if pos is not None else (rec["pos"] if rec else (0.0, 0.0)),
        }
        self._click_up[action] = count
        return count

    def send(self, action, down, *, track=True, flags=0, click_count=None):
        """Hold-style: True only key-down, False only key-up.
        track=False bypasses the held-set (used for combo taps).
        flags = Mac CGEvent modifier mask so shift+space is a chord, not two keys."""
        if not action or action == "none":
            return
        down = bool(down)
        try:
            if action in _MOUSE_DOUBLE:
                if down:
                    base = _MOUSE_DOUBLE[action]
                    self.send(base, True, track=False, flags=flags, click_count=2)
                    time.sleep(0.02)
                    self.send(base, False, track=False, flags=flags, click_count=2)
                return
            if track:
                if down:
                    if action in self._held:
                        return
                    self._held.add(action)
                else:
                    if action not in self._held:
                        return
                    self._held.discard(action)
            if action in _MOUSE_BUTTONS:
                if self._mouse_fn:
                    self._mouse_fn(action, down, flags, click_count)
            elif self._key_fn:
                self._key_fn(action, down, flags)
        except Exception as exc:
            self._error = str(exc)

    def tap(self, combo):
        """Fire a combo once as a real chord: modifiers down (with flags),
        then the rest, then release. Pad CC=0 is ignored by the MIDI side."""
        combo = [a for a in combo if a and a != "none"]
        if not combo:
            return
        if len(combo) == 1 and combo[0] in _MOUSE_DOUBLE:
            self.send(combo[0], True, track=False)
            return
        mods = [m for m in _MOD_ORDER if m in combo]
        rest = [a for a in combo if a not in _MOD_ACTIONS]
        flags = combo_mod_flags(mods)
        for action in combo:
            self._held.discard(action)

        running = 0
        for mod in mods:
            running |= _MAC_MOD_FLAGS.get(mod, 0)
            self.send(mod, True, track=False, flags=running)
        if mods:
            time.sleep(0.03)
        for action in rest:
            self.send(action, True, track=False, flags=flags)
        time.sleep(0.03)
        for action in reversed(rest):
            self.send(action, False, track=False, flags=flags)
        for mod in reversed(mods):
            running &= ~_MAC_MOD_FLAGS.get(mod, 0)
            self.send(mod, False, track=False, flags=running)
        for action in combo:
            self._held.discard(action)

    def _cursor_point(self):
        if self.pointer is not None:
            pos = self.pointer.position()
            if pos is not None:
                return _CGPoint(pos[0], pos[1])
        return None

    def _try_mac(self):
        try:
            cg = ctypes.CDLL(
                "/System/Library/Frameworks/CoreGraphics.framework/CoreGraphics"
            )

            create_key = cg.CGEventCreateKeyboardEvent
            create_key.argtypes = [ctypes.c_void_p, ctypes.c_uint16, ctypes.c_int]
            create_key.restype = ctypes.c_void_p

            create_mouse = cg.CGEventCreateMouseEvent
            create_mouse.argtypes = [
                ctypes.c_void_p, ctypes.c_uint32, _CGPoint, ctypes.c_uint32,
            ]
            create_mouse.restype = ctypes.c_void_p

            create_source = cg.CGEventSourceCreate
            create_source.argtypes = [ctypes.c_int32]
            create_source.restype = ctypes.c_void_p
            key_source = create_source(-1)   # private — keys stay off hardware state
            mouse_source = create_source(1)  # HID — clicks + joystick drags share state
            source = key_source

            post = cg.CGEventPost
            post.argtypes = [ctypes.c_uint32, ctypes.c_void_p]
            post.restype = None

            set_int = cg.CGEventSetIntegerValueField
            set_int.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int64]
            set_int.restype = None

            set_flags = getattr(cg, "CGEventSetFlags", None)
            if set_flags is not None:
                set_flags.argtypes = [ctypes.c_void_p, ctypes.c_uint64]
                set_flags.restype = None

            set_uni = getattr(cg, "CGEventKeyboardSetUnicodeString", None)
            if set_uni is not None:
                set_uni.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_void_p]
                set_uni.restype = None

            get_pos = None
            for libpath in (
                "/System/Library/Frameworks/Carbon.framework/Frameworks/HIToolbox.framework/HIToolbox",
                "/System/Library/Frameworks/Carbon.framework/Carbon",
            ):
                try:
                    hi = ctypes.CDLL(libpath)
                    fn = hi.HIGetMousePosition
                    fn.argtypes = [ctypes.c_uint32, ctypes.c_void_p, ctypes.POINTER(_CGPoint)]
                    fn.restype = ctypes.c_int32
                    get_pos = fn
                    break
                except (OSError, AttributeError):
                    continue

            def _post(ev, flags=0, mouse=False):
                if not ev:
                    return
                # Mouse always HID so a held button + joystick is a real drag.
                # Key combos (flags) HID; single key hold stays on session tap.
                post(self._CG_HID_TAP if (flags or mouse) else self._CG_SESSION_TAP, ev)

            def _cursor():
                pt = self._cursor_point()
                if pt is not None:
                    return pt
                loc = _CGPoint()
                if get_pos is not None and get_pos(2, None, ctypes.byref(loc)) == 0:
                    return loc
                return None

            _mouse_map = {
                ("mouse left", True): (self._CG_LEFT_DOWN, self._CG_BTN_LEFT),
                ("mouse left", False): (self._CG_LEFT_UP, self._CG_BTN_LEFT),
                ("mouse right", True): (self._CG_RIGHT_DOWN, self._CG_BTN_RIGHT),
                ("mouse right", False): (self._CG_RIGHT_UP, self._CG_BTN_RIGHT),
                ("mouse middle", True): (self._CG_OTHER_DOWN, self._CG_BTN_CENTER),
                ("mouse middle", False): (self._CG_OTHER_UP, self._CG_BTN_CENTER),
            }

            def _mouse(action, down, flags=0, click_count=None):
                loc = _cursor()
                if loc is None:
                    self._error = "click: no cursor position"
                    return
                pos = (loc.x, loc.y)
                if down:
                    n = self._next_click_count(action, pos, forced=click_count)
                else:
                    n = click_count or self._click_up.get(action, 1)
                etype, btn = _mouse_map[(action, down)]
                ev = create_mouse(mouse_source, etype, loc, btn)
                if ev:
                    set_int(ev, self._CG_CLICK_STATE_FIELD, int(n))
                    if flags and set_flags is not None:
                        set_flags(ev, flags)
                _post(ev, flags, mouse=True)

            def _key(action, down, flags=0):
                code = _MAC_KEY.get(action)
                if code is None:
                    return
                ev = create_key(source, code, 1 if down else 0)
                if not ev:
                    return
                set_int(ev, 8, 0)  # kCGKeyboardEventAutorepeat = off
                if flags and set_flags is not None:
                    set_flags(ev, flags)
                # Combos: keycode + flags only (no unicode), so shift+space
                # is the shortcut, not a shifted character plus a space.
                # Hold key-up: empty unicode so macOS does not re-type.
                if (flags or not down) and set_uni is not None:
                    set_uni(ev, 0, None)
                _post(ev, flags)

            self._mouse_fn = _mouse
            if self._key_fn is None:
                self._key_fn = _key
        except Exception as exc:
            self._error = str(exc)

    def _try_win(self):
        try:
            INPUT, MOUSEINPUT, KEYBDINPUT = _win_input_types()
            user32 = ctypes.windll.user32
            MapVirtualKeyW = user32.MapVirtualKeyW
            MapVirtualKeyW.argtypes = [ctypes.c_uint, ctypes.c_uint]
            MapVirtualKeyW.restype = ctypes.c_uint
            SendInput = user32.SendInput
            INPUT_MOUSE, INPUT_KEYBOARD = 0, 1
            KEYEVENTF_EXTENDEDKEY = 0x0001
            KEYEVENTF_KEYUP = 0x0002
            KEYEVENTF_SCANCODE = 0x0008
            mouse_flags = {
                ("mouse left", True): 0x0002,
                ("mouse left", False): 0x0004,
                ("mouse right", True): 0x0008,
                ("mouse right", False): 0x0010,
                ("mouse middle", True): 0x0020,
                ("mouse middle", False): 0x0040,
            }

            def _send(inp):
                SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))

            def _mouse(action, down, flags=0, click_count=None):
                flag = mouse_flags[(action, down)]
                inp = INPUT()
                inp.type = INPUT_MOUSE
                inp.mi = MOUSEINPUT(0, 0, 0, flag, 0, None)
                _send(inp)
                if down and click_count and click_count >= 2:
                    up = INPUT()
                    up.type = INPUT_MOUSE
                    up.mi = MOUSEINPUT(0, 0, 0, mouse_flags[(action, False)], 0, None)
                    _send(up)
                    _send(inp)

            def _key(action, down, flags=0):
                vk = _WIN_VK.get(action)
                if vk is None:
                    return
                scan = MapVirtualKeyW(vk, 0)
                kflags = KEYEVENTF_SCANCODE
                if vk in _WIN_VK_EXTENDED:
                    kflags |= KEYEVENTF_EXTENDEDKEY
                if not down:
                    kflags |= KEYEVENTF_KEYUP
                inp = INPUT()
                inp.type = INPUT_KEYBOARD
                inp.ki = KEYBDINPUT(0, scan, kflags, 0, None)
                _send(inp)

            self._mouse_fn = _mouse
            if self._key_fn is None:
                self._key_fn = _key
        except Exception as exc:
            self._error = str(exc)

def _enqueue_input(combo, kind):
    """kind: 'down' | 'up' | 'tap' (or bool for hold mappings)."""
    combo = parse_combo(combo)
    if not combo:
        return
    if kind is True:
        kind = "down"
    elif kind is False:
        kind = "up"
    try:
        input_events.put_nowait((combo, kind))
    except queue.Full:
        pass


# --------------------------
# MIDI Engine
# --------------------------
class MidiFilter:
    def __init__(self, mpk_in, mpk_out, daw_out, virtual_port=None,
                 on_state_change=None, on_log=None, on_init_status=None,
                 on_chord_learned=None, on_clip_learned=None):
        self.inport = mido.open_input(mpk_in)
        self.mpk_out = mido.open_output(mpk_out)
        self.daw_out = daw_out
        self.virtual_port = virtual_port
        self.on_state_change = on_state_change or (lambda *_: None)
        self.on_log = on_log or (lambda *_: None)
        self.on_init_status = on_init_status or (lambda *_: None)
        self.on_chord_learned = on_chord_learned or (lambda *_: None)
        self.on_clip_learned = on_clip_learned or (lambda *_: None)
        self.running = False
        self.proc_thread = None
        self.led_thread = None
        self.pointer = None
        # (src_ch, src_note) -> {kind, out_ch, out_note, vel}
        self.held = {}
        self.held_lock = threading.Lock()
        self._cc13_down = [[False] * 16 for _ in range(4)]
        self._chord_down = [[False] * 16 for _ in range(4)]
        self._chord_sounding = {}
        self._chord_pending = []  # delayed note-ons for humanized playback
        self._chord_learn_cc = [[False] * 16 for _ in range(4)]
        self._chord_learn_tap_at = {}
        self._knob_activity_at = 0.0
        self._chord_learn_lock = threading.Lock()
        self._chord_learn = {}  # (prog, slot) -> set of captured notes
        self._sysex_dumps = queue.Queue(maxsize=16)
        self._init_lock = threading.Lock()
        self._initializing = False

    def _set_led_mode(self, mode):
        with state.lock:
            state.led_mode = mode

    def _fire_cc13(self, prog, slot, down):
        prog = int(prog)
        slot = int(slot)
        if not (0 <= prog <= 3 and 0 <= slot <= 15):
            return
        with state.lock:
            combo = parse_combo(state.progs[prog].cc13_map[slot])
        if not combo:
            self._cc13_down[prog][slot] = bool(down)
            return

        # Combos (2+ keys): tap once on CC>0, ignore CC=0 (re-arm only).
        if not is_hold_mapping(combo):
            if down:
                if self._cc13_down[prog][slot]:
                    return
                self._cc13_down[prog][slot] = True
                _enqueue_input(combo, "tap")
                self._log(f"PROG{prog + 1} CC{slot:02d} TAP → {format_combo(combo)}")
            else:
                self._cc13_down[prog][slot] = False
            return

        # Single key / mouse: CC>0 = down, CC=0 = up
        if down == self._cc13_down[prog][slot]:
            return
        self._cc13_down[prog][slot] = down
        _enqueue_input(combo, "down" if down else "up")
        self._log(
            f"PROG{prog + 1} CC{slot:02d} {'DOWN' if down else 'UP'} → {format_combo(combo)}"
        )

    def _fire_chord(self, prog, slot, down, vel=100):
        prog, slot = int(prog), int(slot)
        if not (0 <= prog <= 3 and 0 <= slot <= 15):
            return
        key = (prog, slot)
        pad_vel = clamp(int(vel), 1, 127)
        if down:
            if self._chord_down[prog][slot]:
                return
            with state.lock:
                cfg = state.progs[prog]
                events = parse_chord(cfg.chord_map[slot])
                use_delay = bool(cfg.chord_delay[slot])
                xpose = int(cfg.chord_xpose[slot])
                local = not bool(cfg.chord_ch_global[slot])
                ch_num = int(cfg.chord_ch[slot]) if local else state.gc
                gk = state.gk
            if not events:
                return
            self._chord_down[prog][slot] = True
            self._chord_pending = [
                p for p in self._chord_pending
                if not (p["prog"] == prog and p["slot"] == slot)
            ]
            sounding = []
            now = time.monotonic()
            out_ch = clamp(ch_num, 1, 16) - 1
            for ev in events:
                out_note = clamp_note(ev["note"] + gk + xpose)
                out_vel = clamp(int(round(ev["vel"] * pad_vel / 127.0)), 1, 127)
                delay = max(0.0, float(ev["delay"])) if use_delay else 0.0
                if delay < 0.001:
                    self._send(mido.Message("note_on", note=out_note,
                                            velocity=out_vel, channel=out_ch))
                    sounding.append((out_ch, out_note))
                else:
                    self._chord_pending.append({
                        "when": now + delay,
                        "prog": prog,
                        "slot": slot,
                        "ch": out_ch,
                        "note": out_note,
                        "vel": out_vel,
                    })
            self._chord_sounding[key] = sounding
            self._log(
                f"PROG{prog + 1} pad CHORD ON → {format_chord(events)} vel={pad_vel}"
            )
            return
        if not self._chord_down[prog][slot]:
            return
        self._chord_down[prog][slot] = False
        self._chord_pending = [
            p for p in self._chord_pending
            if not (p["prog"] == prog and p["slot"] == slot)
        ]
        for out_ch, out_note in self._chord_sounding.pop(key, []):
            self._send(mido.Message("note_off", note=out_note, velocity=0, channel=out_ch))
        self._log(f"PROG{prog + 1} pad CHORD OFF")

    def _fire_clip(self, prog, slot, down, vel=100):
        prog, slot = int(prog), int(slot)
        if not (0 <= prog <= 3 and 0 <= slot <= 15):
            return
        key = (prog, slot)
        pad_vel = clamp(int(vel), 1, 127)
        if down:
            with state.lock:
                cfg = state.progs[prog]
                events = parse_clip(cfg.clip_map[slot])
                use_delay = bool(cfg.clip_delay[slot])
                xpose = int(cfg.clip_xpose[slot])
                mode = cfg.clip_mode[slot] if slot < len(cfg.clip_mode) else "continuous"
            if not events:
                return
            oneshot = mode == "one-shot"
            if self._chord_down[prog][slot]:
                if not oneshot:
                    return
                self._stop_clip_slot(prog, slot, offs=True)
            self._chord_down[prog][slot] = True
            sounding = []
            now = time.monotonic()
            for ev in events:
                out_note = clamp_note(ev["note"] + xpose)
                out_ch = clamp(int(ev.get("ch", 1)), 1, 16) - 1
                out_vel = clamp(int(round(ev["vel"] * pad_vel / 127.0)), 1, 127)
                delay = max(0.0, float(ev["delay"])) if use_delay else 0.0
                dur = max(0.02, float(ev.get("duration", 0.25) or 0.25))
                if delay < 0.001:
                    self._send(mido.Message("note_on", note=out_note,
                                            velocity=out_vel, channel=out_ch))
                    sounding.append((out_ch, out_note))
                else:
                    self._chord_pending.append({
                        "when": now + delay, "prog": prog, "slot": slot,
                        "ch": out_ch, "note": out_note, "vel": out_vel,
                        "kind": "on", "oneshot": oneshot,
                    })
                if oneshot:
                    self._chord_pending.append({
                        "when": now + delay + dur, "prog": prog, "slot": slot,
                        "ch": out_ch, "note": out_note, "vel": 0,
                        "kind": "off", "oneshot": True,
                    })
            self._chord_sounding[key] = sounding
            self._log(
                f"PROG{prog + 1} pad CLIP ON ({mode}) → {format_clip(events)} vel={pad_vel}"
            )
            return
        if not self._chord_down[prog][slot]:
            return
        with state.lock:
            mode = state.progs[prog].clip_mode[slot]
        self._chord_down[prog][slot] = False
        if mode == "one-shot":
            return
        self._stop_clip_slot(prog, slot, offs=True)
        self._log(f"PROG{prog + 1} pad CLIP OFF")

    def _stop_clip_slot(self, prog, slot, offs=True):
        key = (prog, slot)
        self._chord_pending = [
            p for p in self._chord_pending
            if not (p["prog"] == prog and p["slot"] == slot)
        ]
        sounding = self._chord_sounding.pop(key, [])
        if offs:
            for out_ch, out_note in sounding:
                self._send(mido.Message("note_off", note=out_note, velocity=0, channel=out_ch))
        self._chord_down[prog][slot] = False

    def _flush_chord_pending(self):
        if not self._chord_pending:
            return
        now = time.monotonic()
        keep = []
        for ev in self._chord_pending:
            if ev["when"] > now:
                keep.append(ev)
                continue
            prog, slot = ev["prog"], ev["slot"]
            oneshot = bool(ev.get("oneshot"))
            kind = ev.get("kind", "on")
            if kind == "off":
                self._send(mido.Message("note_off", note=ev["note"],
                                        velocity=0, channel=ev["ch"]))
                held = self._chord_sounding.get((prog, slot), [])
                pair = (ev["ch"], ev["note"])
                self._chord_sounding[(prog, slot)] = [x for x in held if x != pair]
                continue
            if not oneshot and not self._chord_down[prog][slot]:
                continue
            self._send(mido.Message("note_on", note=ev["note"],
                                    velocity=ev["vel"], channel=ev["ch"]))
            self._chord_sounding.setdefault((prog, slot), []).append(
                (ev["ch"], ev["note"])
            )
        self._chord_pending = keep

    def _release_chords(self):
        self._chord_pending = []
        for key, sounding in list(self._chord_sounding.items()):
            for out_ch, out_note in sounding:
                self._send(mido.Message("note_off", note=out_note, velocity=0, channel=out_ch))
        self._chord_sounding = {}
        self._chord_down = [[False] * 16 for _ in range(4)]
        with self._chord_learn_lock:
            self._chord_learn = {}
        with state.lock:
            state.chord_learn = None
            if state.led_mode == "learn":
                state.led_mode = "key"

    def _knobs_hot(self):
        return (time.monotonic() - self._knob_activity_at) < KNOB_LEARN_GUARD

    def _arm_chord_learn(self, prog, slot, down):
        """Latch: PC / empty pad tap toggles learn. Ignored while knobs are noisy."""
        prog, slot = int(prog), int(slot)
        if not down:
            self._chord_learn_cc[prog][slot] = False
            return
        if self._knobs_hot():
            return
        if self._chord_learn_cc[prog][slot]:
            return
        self._chord_learn_cc[prog][slot] = True
        key = (prog, slot)
        with self._chord_learn_lock:
            already = key in self._chord_learn
            others = [k for k in self._chord_learn if k != key]
        if already:
            self._commit_chord_learn(prog, slot)
            return
        for op, os in others:
            self._finish_learn(op, os)
        with self._chord_learn_lock:
            self._chord_learn[key] = {
                "t0": None, "events": [], "held": set(), "last": time.monotonic(),
            }
        with state.lock:
            state.chord_learn = key
            state.led_mode = "learn"
        self._log(f"PROG{prog + 1} PC{slot:02d} LEARN latched — play a chord on the keys")

    def _arm_clip_learn(self, prog, slot, down):
        prog, slot = int(prog), int(slot)
        if not down:
            self._chord_learn_cc[prog][slot] = False
            return
        if self._knobs_hot():
            return
        if self._chord_learn_cc[prog][slot]:
            return
        self._chord_learn_cc[prog][slot] = True
        key = (prog, slot)
        with self._chord_learn_lock:
            already = key in self._chord_learn
            others = [k for k in self._chord_learn if k != key]
        if already:
            self._finish_learn(prog, slot)
            return
        for op, os in others:
            self._finish_learn(op, os)
        with state.lock:
            overdub = bool(state.clip_overdub[prog])
            base = parse_clip(state.progs[prog].clip_map[slot]) if overdub else []
        with self._chord_learn_lock:
            self._chord_learn[key] = {
                "t0": None, "events": [], "held": set(), "last": time.monotonic(),
                "clip": True, "overdub": overdub, "base": base,
            }
        with state.lock:
            state.chord_learn = key
            state.led_mode = "learn"
        verb = "OVERDUB" if overdub else "LEARN"
        self._log(f"PROG{prog + 1} Pad {slot + 1} CLIP {verb} — play notes on any channel")

    def _arm_clip_learn_tap(self, prog, slot):
        if self._knobs_hot():
            return
        prog, slot = int(prog), int(slot)
        now = time.monotonic()
        key = (prog, slot)
        last = self._chord_learn_tap_at.get(key, 0.0)
        if now - last < CHORD_LEARN_TAP_DEBOUNCE:
            return
        self._chord_learn_tap_at[key] = now
        self._arm_clip_learn(prog, slot, True)
        self._arm_clip_learn(prog, slot, False)

    def _finish_learn(self, prog, slot):
        key = (int(prog), int(slot))
        with self._chord_learn_lock:
            rec = self._chord_learn.get(key)
        if rec and rec.get("clip"):
            self._commit_clip_learn(prog, slot)
        else:
            self._commit_chord_learn(prog, slot)

    def _clear_clip_slot(self, prog, slot):
        prog, slot = int(prog), int(slot)
        key = (prog, slot)
        with self._chord_learn_lock:
            rec = self._chord_learn.pop(key, None)
        self._stop_clip_slot(prog, slot, offs=True)
        with state.lock:
            state.progs[prog].clip_map[slot] = []
            if state.chord_learn == key:
                state.chord_learn = None
            if state.led_mode == "learn":
                state.led_mode = "key"
        try:
            self.on_clip_learned(prog, slot, [])
        except Exception:
            pass
        extra = " (learn cancelled)" if rec else ""
        self._log(f"PROG{prog + 1} Pad {slot + 1} CLIP cleared{extra}")

    def _commit_clip_learn(self, prog, slot):
        key = (int(prog), int(slot))
        with self._chord_learn_lock:
            rec = self._chord_learn.pop(key, None)
        with state.lock:
            if state.chord_learn == key:
                state.chord_learn = None
            state.led_mode = "key"
        if rec is None:
            return
        now = time.monotonic()
        t0 = rec.get("t0") or now
        for (src_ch, src_note), info in list(rec.get("held_at", {}).items()):
            t_on, ev_ch, ev_note = info if isinstance(info, tuple) and len(info) == 3 else (now, src_ch, src_note)
            for ev in rec["events"]:
                if ev["note"] == ev_note and ev["ch"] == ev_ch and ev.get("duration") is None:
                    ev["duration"] = max(0.02, now - t_on)
                    break
        new = parse_clip(rec.get("events"))
        if not new:
            self._log(f"PROG{prog + 1} Pad {slot + 1} CLIP LEARN off — no notes, slot unchanged")
            return
        with state.lock:
            if rec.get("overdub"):
                notes = merge_clip_events(rec.get("base") or [], new)
            else:
                notes = new
            state.progs[prog].clip_map[slot] = [dict(e) for e in notes]
        try:
            self.on_clip_learned(prog, slot, notes)
        except Exception:
            pass
        verb = "OVERDUB" if rec.get("overdub") else "LEARN"
        self._log(f"PROG{prog + 1} Pad {slot + 1} CLIP {verb} → {format_clip(notes)}")

    def _arm_chord_learn_tap(self, prog, slot):
        """One-shot latch (program change / empty pad). Debounced; ignored during knob noise."""
        if self._knobs_hot():
            return
        prog, slot = int(prog), int(slot)
        now = time.monotonic()
        key = (prog, slot)
        last = self._chord_learn_tap_at.get(key, 0.0)
        if now - last < CHORD_LEARN_TAP_DEBOUNCE:
            return
        self._chord_learn_tap_at[key] = now
        self._arm_chord_learn(prog, slot, True)
        self._arm_chord_learn(prog, slot, False)

    def _select_key_channel(self, ch, src=""):
        ch = clamp(int(ch), 1, 16)
        old = state.gc
        with state.lock:
            state.gc = ch
            state.blink_high = state.gc > 8
            if state.chord_learn is None:
                state.led_mode = "key"
        if old != state.gc:
            extra = f" ({src})" if src else ""
            self._log(f"key ch {old}->{state.gc}{extra}")

    def _select_pad_channel(self, ch, src=""):
        ch = clamp(int(ch), 1, 16)
        old = state.gd
        with state.lock:
            state.gd = ch
            state.led_mode = "pad"
        if old != state.gd:
            extra = f" ({src})" if src else ""
            self._log(f"pad ch {old}->{state.gd}{extra}")

    def _commit_chord_learn(self, prog, slot):
        key = (int(prog), int(slot))
        with self._chord_learn_lock:
            rec = self._chord_learn.pop(key, None)
        if rec and rec.get("clip"):
            with self._chord_learn_lock:
                self._chord_learn[key] = rec
            self._commit_clip_learn(prog, slot)
            return
        with state.lock:
            if state.chord_learn == key:
                state.chord_learn = None
            state.led_mode = "key"
        if rec is None:
            return
        notes = parse_chord(rec.get("events"))
        if not notes:
            self._log(f"PROG{prog + 1} PC{slot:02d} LEARN off — no keys, slot unchanged")
            return
        with state.lock:
            state.progs[prog].chord_map[slot] = [dict(e) for e in notes]
        try:
            self.on_chord_learned(prog, slot, notes)
        except Exception:
            pass
        self._log(f"PROG{prog + 1} PC{slot:02d} LEARN → {format_chord(notes)}")

    def _flush_chord_learn(self):
        if not self._chord_learn:
            return
        now = time.monotonic()
        ready = []
        with self._chord_learn_lock:
            for key, rec in list(self._chord_learn.items()):
                if rec["events"] and not rec["held"]:
                    last = rec.get("last", rec.get("t0") or now)
                    if now - last >= CHORD_LEARN_SETTLE:
                        ready.append(key)
        for p, sl in ready:
            self._finish_learn(p, sl)

    def _capture_learn_note(self, note, vel=100, down=True, ch=0):
        note = clamp_note(note)
        ch = clamp(int(ch), 0, 15)
        now = time.monotonic()
        with state.lock:
            gk, pk, gc, gd = state.gk, state.pk, state.gc, state.gd
        if PAD_CH_LO <= ch <= PAD_CH_HI:
            out_ch = clamp(int(gd), 1, 16)
            out_note = clamp_note((note - 60) + pk)
        elif 0 <= ch <= 3:
            out_ch = clamp(int(gc), 1, 16)
            out_note = clamp_note(note + gk)
        else:
            out_ch = ch + 1
            out_note = note
        with self._chord_learn_lock:
            if not self._chord_learn:
                return
            snapshot = []
            clip_snap = []
            for (p, sl), rec in self._chord_learn.items():
                if rec.get("clip"):
                    src_key = (ch, note)
                    held_at = rec.setdefault("held_at", {})
                    if down:
                        rec["held"].add(src_key)
                        rec["last"] = now
                        vel = clamp(int(vel), 1, 127)
                        if rec["t0"] is None:
                            rec["t0"] = now
                            delay = 0.0
                        else:
                            delay = max(0.0, now - rec["t0"])
                        rec["events"].append({
                            "note": out_note, "delay": delay, "vel": vel,
                            "ch": out_ch, "duration": None,
                        })
                        held_at[src_key] = (now, out_ch, out_note)
                    else:
                        rec["held"].discard(src_key)
                        rec["last"] = now
                        info = held_at.pop(src_key, None)
                        if info:
                            t_on, ev_ch, ev_note = info
                        else:
                            t_on, ev_ch, ev_note = rec.get("t0") or now, out_ch, out_note
                        for ev in reversed(rec["events"]):
                            if (ev["note"] == ev_note and ev["ch"] == ev_ch
                                    and ev.get("duration") is None):
                                ev["duration"] = max(0.02, now - t_on)
                                break
                    clip_snap.append((p, sl, parse_clip(rec["events"])))
                    continue
                if not (0 <= ch <= 3):
                    continue
                if down:
                    rec["held"].add(note)
                    rec["last"] = now
                    seen = {e["note"] for e in rec["events"]}
                    if note not in seen:
                        vel = clamp(int(vel), 1, 127)
                        if rec["t0"] is None:
                            rec["t0"] = now
                            delay = 0.0
                        else:
                            delay = max(0.0, now - rec["t0"])
                        rec["events"].append({"note": note, "delay": delay, "vel": vel})
                else:
                    rec["held"].discard(note)
                    rec["last"] = now
                snapshot.append((p, sl, parse_chord(rec["events"])))
        for p, sl, notes in snapshot:
            if not notes:
                continue
            with state.lock:
                state.progs[p].chord_map[sl] = [dict(e) for e in notes]
            try:
                self.on_chord_learned(p, sl, notes)
            except Exception:
                pass
        for p, sl, notes in clip_snap:
            if not notes:
                continue
            with state.lock:
                base = []
                with self._chord_learn_lock:
                    rec = self._chord_learn.get((p, sl))
                    if rec and rec.get("overdub"):
                        base = list(rec.get("base") or [])
                notes = merge_clip_events(base, notes) if base else notes
                state.progs[p].clip_map[sl] = [dict(e) for e in notes]
            try:
                self.on_clip_learned(p, sl, notes)
            except Exception:
                pass

    def _state_changed(self):
        # GUI poller copies counters. Do not touch Tk from the MIDI thread
        # (ttk.Spinbox + negative transpose was crashing Aqua Tk on macOS).
        pass

    def _log(self, text):
        self.on_log(text)

    def _send(self, msg):
        if self.daw_out:
            self.daw_out.send(msg)
        if self.virtual_port:
            self.virtual_port.send(msg)

    def start(self):
        self.running = True
        stop_event.clear()
        with state.lock:
            state.blink_high = state.gc > 8
            state.axis_x = 0.0
            state.axis_y = 0.0
            state.led_mode = "key"
        self._cc13_down = [[False] * 16 for _ in range(4)]
        self._chord_down = [[False] * 16 for _ in range(4)]
        self._chord_sounding = {}
        self._chord_pending = []
        self._chord_learn_cc = [[False] * 16 for _ in range(4)]
        self._chord_learn_tap_at = {}
        self._knob_activity_at = 0.0
        with self._chord_learn_lock:
            self._chord_learn = {}
        with state.lock:
            state.chord_learn = None
            if state.led_mode == "learn":
                state.led_mode = "key"
        self.proc_thread = threading.Thread(target=self.process_loop, daemon=True)
        self.proc_thread.start()
        self.led_thread = threading.Thread(target=self.led_feedback_loop, daemon=True)
        self.led_thread.start()
        self._log("Filter started.")

    def stop(self):
        self.running = False
        stop_event.set()
        with state.lock:
            state.axis_x = 0.0
            state.axis_y = 0.0
        self._release_cc13()
        self._release_chords()
        with self._chord_learn_lock:
            self._chord_learn = {}
        self.panic()
        for th in (self.proc_thread, self.led_thread):
            if th:
                try:
                    th.join(timeout=1.0)
                except Exception:
                    pass
        for port in (self.inport, self.mpk_out, self.daw_out, self.virtual_port):
            if port:
                try:
                    port.close()
                except Exception:
                    pass
        self.inport = self.mpk_out = self.daw_out = self.virtual_port = None
        self._log("Filter stopped.")

    def _release_cc13(self):
        with state.lock:
            maps = [[parse_combo(c) for c in p.cc13_map] for p in state.progs]
        for prog in range(4):
            for i, down in enumerate(self._cc13_down[prog]):
                if down and is_hold_mapping(maps[prog][i]):
                    _enqueue_input(maps[prog][i], "up")
                self._cc13_down[prog][i] = False

    # ----- sounding-note table -----
    # Mapping is captured at note-on. Transpose / channel changes never
    # re-voice held notes; note-off always uses the original out note/channel.
    def _sound_on(self, kind, src_ch, src_note, vel):
        if vel <= 0:
            self._sound_off(src_ch, src_note)
            return
        with state.lock:
            gk, pk, gc, gd = state.gk, state.pk, state.gc, state.gd
        if kind == "key":
            out_ch = gc - 1
            out_note = clamp_note(src_note + gk)
        else:
            out_ch = gd - 1
            out_note = clamp_note((src_note - 60) + pk)
        key = (src_ch, src_note)
        with self.held_lock:
            prev = self.held.get(key)
            if prev:
                self._send(mido.Message("note_off", note=prev["out_note"],
                                        velocity=0, channel=prev["out_ch"]))
            self.held[key] = {
                "kind": kind, "out_ch": out_ch, "out_note": out_note, "vel": vel,
            }
        self._send(mido.Message("note_on", note=out_note, velocity=vel, channel=out_ch))

    def _sound_off(self, src_ch, src_note):
        key = (src_ch, src_note)
        with self.held_lock:
            prev = self.held.pop(key, None)
        if not prev:
            return
        self._send(mido.Message("note_off", note=prev["out_note"],
                                velocity=0, channel=prev["out_ch"]))

    def panic(self):
        with self.held_lock:
            sounding = list(self.held.values())
            self.held.clear()
        sent_ch = set()
        for prev in sounding:
            self._send(mido.Message("note_off", note=prev["out_note"],
                                    velocity=0, channel=prev["out_ch"]))
            sent_ch.add(prev["out_ch"])
        for ch in set(list(sent_ch) + [state.gc - 1, state.gd - 1]):
            try:
                self._send(mido.Message("control_change", control=123, value=0, channel=ch))
            except Exception:
                pass
        self._release_cc13()
        self._release_chords()

    # --------------------------
    # Processing Loop
    # --------------------------
    def process_loop(self):
        while self.running and not stop_event.is_set():
            try:
                pending = list(self.inport.iter_pending()) if self.inport else []
            except Exception as e:
                if self.running:
                    self._log(f"Input error: {e}")
                break
            if not pending:
                self._flush_chord_pending()
                self._flush_chord_learn()
                time.sleep(0.001)
                continue
            for msg in pending:
                if not self.running:
                    break
                try:
                    if msg.type == "sysex":
                        self._on_sysex(msg)
                    else:
                        self._handle(msg)
                except Exception as e:
                    self._log(f"Process error: {e}")
            self._flush_chord_pending()
            self._flush_chord_learn()

    def _handle(self, msg):
        # Drum pads: notes on ch 10-13. Chord-macro PROGs play slots on Key Channel;
        # every other PROG flattens to the Pad Channel.
        if msg.type in ("note_on", "note_off") and PAD_CH_LO <= msg.channel <= PAD_CH_HI:
            prog = msg.channel - 9
            with state.lock:
                pad_preset = state.progs[prog].pad_preset
            down = not (msg.type == "note_off" or msg.velocity == 0)
            if pad_preset == PRESET_CHORD:
                slot = pad_note_to_slot(msg.note)
                if slot is None:
                    return
                with state.lock:
                    empty = not parse_chord(state.progs[prog].chord_map[slot])
                with self._chord_learn_lock:
                    learning = (prog, slot) in self._chord_learn
                if empty or learning:
                    if down:
                        self._arm_chord_learn_tap(prog, slot)
                    return
                if down:
                    self._set_led_mode("key")
                self._fire_chord(prog, slot, down, vel=msg.velocity)
                return
            if pad_preset == PRESET_CLIP:
                slot = pad_note_to_slot(msg.note)
                if slot is None:
                    return
                with self._chord_learn_lock:
                    learning = (prog, slot) in self._chord_learn
                if learning:
                    return
                with state.lock:
                    empty = not parse_clip(state.progs[prog].clip_map[slot])
                if empty:
                    return
                self._fire_clip(prog, slot, down, vel=msg.velocity)
                return
            self._set_led_mode("pad")
            if down:
                self._sound_on("pad", msg.channel, msg.note, msg.velocity)
            else:
                self._sound_off(msg.channel, msg.note)
            self._capture_learn_note(msg.note, msg.velocity, down, ch=msg.channel)
            return

        # Pad-bank CCs on ch 10-13 follow that PROG's preset
        if msg.type == "control_change" and PAD_CH_LO <= msg.channel <= PAD_CH_HI:
            if 0 <= msg.control <= 15:
                self._handle_pad_cc(msg)
            return

        # Sustain → key channel
        if msg.type == "control_change" and msg.control == 64:
            self._send(mido.Message("control_change", control=64, value=msg.value,
                                    channel=state.gc - 1))
            if msg.value in (0, 127):
                self._log(f"Sustain → key ch {state.gc} value={msg.value}")
            return

        # Joystick channels 1-4: behavior follows that PROG's preset
        if 0 <= msg.channel <= 3:
            with state.lock:
                joy = state.progs[msg.channel].joy_preset
            if msg.type == "pitchwheel":
                if joy == PRESET_PTR:
                    with state.lock:
                        state.pointer_prog = msg.channel
                    self._set_axis_x(msg.pitch / 8191.0)
                else:
                    self._send(mido.Message("pitchwheel", pitch=msg.pitch,
                                            channel=state.gc - 1))
                return
            if msg.type == "control_change":
                if msg.control == 64 or 20 <= msg.control <= 27:
                    pass  # knobs / sustain handled below
                elif joy == PRESET_PTR:
                    if msg.control == JOY_CC_Y:
                        with state.lock:
                            state.pointer_prog = msg.channel
                        self._set_axis_y((msg.value - 64) / 64.0)
                    elif msg.control in (JOY_CC_A, JOY_CC_B):
                        self._handle_joystick_cc(msg)
                    return
                elif msg.control in (JOY_CC_A, JOY_CC_B):
                    self._handle_joystick_cc(msg)
                    return
                elif msg.control == JOY_CC_Y and joy == PRESET_MW:
                    self._send(mido.Message("control_change", control=1,
                                            value=msg.value, channel=state.gc - 1))
                    return

        # Keys ch1-4 → key channel + key transpose
        if msg.type in ("note_on", "note_off") and 0 <= msg.channel <= 3:
            self._set_led_mode("key")
            down = not (msg.type == "note_off" or msg.velocity == 0)
            self._capture_learn_note(msg.note, msg.velocity, down, ch=msg.channel)
            if not down:
                self._sound_off(msg.channel, msg.note)
            else:
                self._sound_on("key", msg.channel, msg.note, msg.velocity)
            return

        # Program change: chord PROGs use PC 0–15 as Learn; ch10 otherwise passthrough
        if msg.type == "program_change":
            if PAD_CH_LO <= msg.channel <= PAD_CH_HI:
                prog = msg.channel - 9
                with state.lock:
                    pad_preset = state.progs[prog].pad_preset
                if pad_preset == PRESET_CHORD and 0 <= msg.program <= 15:
                    self._arm_chord_learn_tap(prog, msg.program)
                    return
                if pad_preset == PRESET_CLIP and 0 <= msg.program <= 15:
                    self._clear_clip_slot(prog, msg.program)
                    return
            if msg.channel == 9:
                with state.lock:
                    state.current_program = msg.program
                self._send(mido.Message("program_change", program=msg.program,
                                        channel=state.gc - 1))
                self._log(f"Program change passthru → PC {msg.program} on ch {state.gc}")
            return

        # Knobs CC20..27 on ch1..4 — always the current knob bank, any preset
        if msg.type == "control_change" and 0 <= msg.channel <= 3:
            if 20 <= msg.control <= 27:
                self._knob_activity_at = time.monotonic()
                knob = msg.control - 20
                with state.lock:
                    bank = state.knob_bank - 1
                    out_cc = state.knob_ccs[bank][knob]
                    if state.knob_ch_global[bank]:
                        out_ch = state.gc - 1
                    else:
                        row = state.knob_ch[bank]
                        if isinstance(row, (list, tuple)):
                            out_ch = clamp(row[knob], 1, 16) - 1
                        else:
                            out_ch = clamp(row, 1, 16) - 1
                self._send(mido.Message("control_change", control=out_cc,
                                        value=msg.value, channel=out_ch))
            return

    def _handle_pad_cc(self, msg):
        cc, val, ch = msg.control, msg.value, msg.channel
        if not (0 <= cc <= 15 and PAD_CH_LO <= ch <= PAD_CH_HI):
            return
        prog = ch - 9
        with state.lock:
            cfg = state.progs[prog]
            pad_preset = cfg.pad_preset
            cc_map = list(cfg.cc_map)
            cc_global = bool(cfg.cc_ch_global)
            cc_ch = int(cfg.cc_ch)

        if pad_preset == PRESET_MW:
            out_ch = (state.gd if cc_global else clamp(cc_ch, 1, 16)) - 1
            self._send(mido.Message("control_change", control=cc_map[cc],
                                    value=val, channel=out_ch))
            return
        if pad_preset == PRESET_KEY:
            if val == 0:
                return
            self._select_key_channel(cc + 1, src=f"PROG{prog + 1} pad CC")
            return
        if pad_preset == PRESET_PAD:
            if val == 0:
                return
            self._select_pad_channel(cc + 1, src=f"PROG{prog + 1} pad CC")
            return
        if pad_preset == PRESET_PTR:
            self._fire_cc13(prog, cc, val > 0)
            return
        if pad_preset == PRESET_KNOB:
            if val == 0:
                return
            old = state.knob_bank
            with state.lock:
                state.knob_bank = cc + 1
            if old != state.knob_bank:
                name = state.knob_bank_names[state.knob_bank - 1]
                self._log(f"PROG{prog + 1} pad CC → knob bank {old}->{state.knob_bank} ({name})")
            return
        if pad_preset == PRESET_CHORD:
            if val == 0:
                return
            self._select_key_channel(cc + 1, src=f"PROG{prog + 1} pad CC")
            return
        if pad_preset == PRESET_CLIP:
            if val == 0:
                return
            self._arm_clip_learn_tap(prog, cc)
            return

    def _handle_joystick_cc(self, msg):
        ch = msg.channel
        if not (0 <= ch <= 3):
            return
        inc = msg.control == JOY_CC_B  # 31 = up / A-side, 30 = down / B-side
        with state.lock:
            cfg = state.progs[ch]
            joy = cfg.joy_preset
            cc_a, cc_b = cfg.cc_a, cfg.cc_b

        if joy == PRESET_MW:
            out_cc = cc_a if msg.control == JOY_CC_A else cc_b
            self._send(mido.Message("control_change", control=out_cc,
                                    value=msg.value, channel=state.gc - 1))
            return
        if joy == PRESET_KEY and msg.value == 127:
            with state.lock:
                state.gk = clamp(state.gk + (1 if inc else -1), TRANSPOSE_MIN, TRANSPOSE_MAX)
            self._state_changed()
            self._log(f"Key transpose {'up' if inc else 'down'} → {state.gk}")
            return
        if joy == PRESET_PAD and msg.value == 127:
            with state.lock:
                state.pk = clamp(state.pk + (1 if inc else -1), TRANSPOSE_MIN, TRANSPOSE_MAX)
            self._state_changed()
            self._log(f"Pad transpose {'up' if inc else 'down'} → {state.pk}")
            return
        if joy == PRESET_KEY_CH and msg.value == 127:
            nxt = clamp(state.gc + (1 if inc else -1), 1, 16)
            self._select_key_channel(nxt, src=f"PROG{ch + 1} stick")
            return
        if joy == PRESET_PAD_CH and msg.value == 127:
            nxt = clamp(state.gd + (1 if inc else -1), 1, 16)
            self._select_pad_channel(nxt, src=f"PROG{ch + 1} stick")
            return
        if joy == PRESET_PTR:
            with state.lock:
                state.pointer_prog = ch
            if msg.control == JOY_CC_A:
                self._set_axis_y(-1.0 if msg.value >= 64 else 0.0)
            else:
                self._set_axis_y(1.0 if msg.value >= 64 else 0.0)

    def _set_axis_x(self, v):
        v = clamp(v, -1.0, 1.0)
        if abs(v) < DEADZONE:
            v = 0.0
        with state.lock:
            state.axis_x = v

    def _set_axis_y(self, v):
        # MIDI up (CC 127 / joystick up) should move the cursor up (negative screen Y)
        v = clamp(v, -1.0, 1.0)
        if abs(v) < DEADZONE:
            v = 0.0
        with state.lock:
            state.axis_y = -v

    # --------------------------
    # LED Feedback
    # --------------------------
    def led_feedback_loop(self):
        pad_notes = list(range(9, 17))
        tick = 0
        while self.running and not stop_event.is_set():
            try:
                with state.lock:
                    learn = state.chord_learn
                    shown = state.gd if state.led_mode == "pad" else state.gc
                if learn is not None:
                    pad_i = int(learn[1]) % 8
                    flash_on = (tick % 2 == 0)
                    for i, note in enumerate(pad_notes):
                        vel = 127 if (i == pad_i and flash_on) else 1
                        if self.mpk_out:
                            self.mpk_out.send(mido.Message("note_on", note=note,
                                                           velocity=vel, channel=0))
                    time.sleep(0.06)
                else:
                    index = (shown - 1) % 8
                    blink_high = shown > 8
                    blink_on = (tick % 2 == 0)
                    for i, note in enumerate(pad_notes):
                        vel = 127 if (i == index and (not blink_high or blink_on)) else 1
                        if self.mpk_out:
                            self.mpk_out.send(mido.Message("note_on", note=note,
                                                           velocity=vel, channel=0))
                    time.sleep(0.14)
            except Exception:
                time.sleep(0.14)
            tick += 1

    def initialize_mpk(self):
        if not self.mpk_out:
            self._log("Initialize: MPK output is closed.")
            return
        with self._init_lock:
            if self._initializing:
                self._log("Initialize already running.")
                return
            self._initializing = True
        self._report_init(None, "pending")
        threading.Thread(target=self._initialize_worker, daemon=True).start()

    def _report_init(self, prog, status):
        try:
            self.on_init_status(prog, status)
        except Exception:
            pass

    def _on_sysex(self, msg):
        data = list(msg.data)
        if len(data) >= 7 and tuple(data[0:3]) == _SYSEX_HDR and data[3] == 0x67:
            try:
                self._sysex_dumps.put_nowait(data)
            except queue.Full:
                pass

    def _drain_sysex(self):
        while True:
            try:
                self._sysex_dumps.get_nowait()
            except queue.Empty:
                break

    def _request_dump(self, prog, timeout=1.5):
        self._drain_sysex()
        if not self.mpk_out:
            return None
        self.mpk_out.send(mido.Message("sysex", data=_sysex_request(prog)))
        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                data = self._sysex_dumps.get(timeout=0.05)
            except queue.Empty:
                continue
            if len(data) > 6 and data[6] == prog:
                return data
        return None

    def _write_dump(self, prog):
        if not self.mpk_out:
            return
        self.mpk_out.send(mido.Message("sysex", data=_sysex_write(prog)))
        time.sleep(0.2)

    def _describe_dump(self, data):
        if not data or len(data) < 9:
            return "(empty)"
        return (
            f"PROG {data[6]}  key/joy ch {data[8] + 1}  pad ch {data[7] + 1}"
        )

    def _initialize_worker(self):
        try:
            self._log("Initialize: requesting PROG 1–4 dumps…")
            ok = 0
            for prog in range(1, 5):
                dump = self._request_dump(prog)
                if dump is None:
                    self._log(f"PROG {prog}: no reply — writing expected config")
                    self._write_dump(prog)
                    dump = self._request_dump(prog)
                if dump is not None and _sysex_dump_ok(dump, prog):
                    self._log(f"PROG {prog}: OK  ({self._describe_dump(dump)})")
                    self._report_init(prog - 1, "ok")
                    ok += 1
                    continue
                if dump is None:
                    self._log(f"PROG {prog}: still no reply after write")
                    self._report_init(prog - 1, "fail")
                    continue
                self._log(
                    f"PROG {prog}: mismatch ({self._describe_dump(dump)}) — writing expected config"
                )
                self._write_dump(prog)
                dump = self._request_dump(prog)
                if dump is not None and _sysex_dump_ok(dump, prog):
                    self._log(f"PROG {prog}: confirmed after write  ({self._describe_dump(dump)})")
                    self._report_init(prog - 1, "ok")
                    ok += 1
                elif dump is None:
                    self._log(f"PROG {prog}: no reply after write")
                    self._report_init(prog - 1, "fail")
                else:
                    self._log(f"PROG {prog}: still mismatch  ({self._describe_dump(dump)})")
                    self._report_init(prog - 1, "fail")
            self._log(f"Initialize complete: {ok}/4 PROG dumps match.")
        except Exception as e:
            self._log(f"Initialize error: {e}")
            self._report_init(None, "fail")
        finally:
            with self._init_lock:
                self._initializing = False


def make_spin(parent, var, lo, hi, on_change=None, width=3):
    """Same ttk up/down spin used by K1–K8."""
    sp = ttk.Spinbox(
        parent, from_=lo, to=hi, textvariable=var, width=width,
        command=on_change,
    )
    if on_change:
        sp.bind("<Return>", lambda e: on_change())
        sp.bind("<FocusOut>", lambda e: on_change())
    return sp


class ChordNameSpin(tk.Frame):
    """Spinbox whose field shows the chord name; arrows transpose the slot."""

    NAME_BG = "#ffffff"
    NAME_FG = "#111111"
    X_FG = "#555555"

    def __init__(self, master, name_var, xpose_var, on_xpose, on_clear, prog, slot, gui,
                 kind="chord"):
        super().__init__(master)
        self._spin = ttk.Spinbox(
            self, from_=TRANSPOSE_MIN, to=TRANSPOSE_MAX,
            textvariable=xpose_var, width=12, command=on_xpose, takefocus=0,
        )
        self._spin.pack(fill="both", expand=True)
        self._spin.bind("<Return>", lambda e: on_xpose())
        self._spin.bind("<FocusOut>", lambda e: on_xpose())
        bg, fg = self.NAME_BG, self.NAME_FG
        self._cover = tk.Frame(self, bg=bg, highlightthickness=0, bd=0)
        self._lab = tk.Label(
            self._cover, textvariable=name_var, anchor="w", bd=0, bg=bg, fg=fg,
            cursor="hand2", highlightthickness=0,
        )
        self._lab.pack(side="left", fill="both", expand=True, padx=(4, 0))
        self._x = tk.Label(
            self._cover, text="×", fg=self.X_FG, bg=bg, cursor="hand2", bd=0, padx=3,
            highlightthickness=0,
        )
        self._x.pack(side="right")
        self._x.bind("<Button-1>", lambda e: on_clear())
        self._lab._name_bg = bg
        self._lab._name_fg = fg
        self._cover._name_bg = bg
        self._cover._name_fg = fg
        ref = (prog, slot)
        if kind == "clip":
            self._clip_ref = ref
            self._lab._clip_ref = ref
            self._cover._clip_ref = ref
            self._lab.bind("<ButtonPress-1>", lambda e: gui._clip_press(prog, slot, e))
            self._lab.bind("<ButtonRelease-1>", gui._clip_release)
            self._cover.bind("<ButtonPress-1>", lambda e: gui._clip_press(prog, slot, e))
            self._cover.bind("<ButtonRelease-1>", gui._clip_release)
        else:
            self._chord_ref = ref
            self._lab._chord_ref = ref
            self._cover._chord_ref = ref
            self._lab.bind("<ButtonPress-1>", lambda e: gui._chord_press(prog, slot, e))
            self._lab.bind("<ButtonRelease-1>", gui._chord_release)
            self._cover.bind("<ButtonPress-1>", lambda e: gui._chord_press(prog, slot, e))
            self._cover.bind("<ButtonRelease-1>", gui._chord_release)
        self.bind("<Configure>", self._place_cover)
        self._spin.bind("<Configure>", self._place_cover)
        self.after_idle(self._place_cover)

    def _place_cover(self, _e=None):
        w = self.winfo_width()
        h = self.winfo_height()
        if w < 10 or h < 8:
            return
        gap = 20
        self._cover.place(x=2, y=1, width=max(10, w - gap - 3), height=max(8, h - 2))


# --------------------------
# GUI
# --------------------------
class MidiGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("MiniMapper")
        self.root.minsize(1, 1)
        self.filter = None
        self._syncing = False
        self._last_ui = None
        self.pointer = PointerDriver()
        self.hid = InputDriver(pointer=self.pointer)
        self._frac_x = 0.0
        self._frac_y = 0.0
        self._pointer_warned = False
        self._hid_warned = False
        self._dpad_held = None  # current arrow action or None
        self._kb_drag = None
        self.prog_ui = []
        self.log = None
        ensure_mapper_state()

        row = 0
        io_head = tk.Frame(root)
        io_head.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=(4, 0))
        self._io_shown = True
        self._io_toggle = tk.Button(
            io_head, text="▾  I/O", command=self._toggle_io,
            bd=0, highlightthickness=0, takefocus=0, font=("Helvetica", 12, "bold"), fg="#333",
        )
        self._io_toggle.pack(side="left")
        row += 1
        top = tk.Frame(root)
        self._io_body = top
        top.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=2)
        tk.Label(top, text="MPK:").pack(side="left")
        self.mpk_status_var = tk.StringVar(value="Disconnected")
        self.mpk_status_label = tk.Label(top, textvariable=self.mpk_status_var, fg="red")
        self.mpk_status_label.pack(side="left", padx=(2, 10))
        tk.Label(top, text="Sync:").pack(side="left")
        self._sync_dots = []
        for i in range(4):
            dot = tk.Label(top, text="●", fg="#cc3333", font=("Helvetica", 12))
            dot.pack(side="left", padx=1)
            self._sync_dots.append(dot)
        tk.Label(top, text="To DAW:").pack(side="left", padx=(12, 2))
        virt_vals, virt_default, extra_vals = self._port_choices()
        self.virt_out_var = tk.StringVar(value=virt_default)
        self.virt_out_combo = ttk.Combobox(
            top, textvariable=self.virt_out_var, values=virt_vals, width=22,
        )
        self.virt_out_combo.pack(side="left")
        tk.Label(top, text="Also:").pack(side="left", padx=(8, 2))
        self.daw_out_var = tk.StringVar(value="None")
        self.daw_out_combo = ttk.Combobox(
            top, textvariable=self.daw_out_var, values=extra_vals, width=18,
        )
        self.daw_out_combo.pack(side="left")
        self.start_btn = tk.Button(top, text="Start", command=self.start_filter, width=7)
        self.start_btn.pack(side="left", padx=(8, 2))
        self.stop_btn = tk.Button(top, text="Stop", command=self.stop_filter, width=7, state="disabled")
        self.stop_btn.pack(side="left", padx=2)
        self.panic_btn = tk.Button(top, text="Panic", command=self.panic, width=7, state="disabled")
        self.panic_btn.pack(side="left", padx=2)
        self.refresh_btn = tk.Button(top, text="Ports", command=self.refresh_ports, width=6)
        self.refresh_btn.pack(side="left", padx=2)
        row += 1

        glob_head = tk.Frame(root)
        glob_head.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=(4, 0))
        self._glob_shown = True
        self._glob_toggle = tk.Button(
            glob_head, text="▾  Global", command=self._toggle_global,
            bd=0, highlightthickness=0, takefocus=0, font=("Helvetica", 12, "bold"), fg="#333",
        )
        self._glob_toggle.pack(side="left")
        row += 1
        counters = tk.Frame(root)
        self._glob_body = counters
        counters.grid(row=row, column=0, columnspan=2, sticky="w", padx=6, pady=2)

        keys = tk.Frame(counters)
        keys.grid(row=0, column=0, sticky="nw", padx=(0, 16))
        tk.Label(keys, text="Key Ch:").grid(row=0, column=0, sticky="e", padx=(0, 2))
        self.gc_var = tk.IntVar(value=state.gc)
        make_spin(keys, self.gc_var, 1, 16, self._on_gc_spin).grid(row=0, column=1, padx=2)
        tk.Label(keys, text="Key Transpose:").grid(row=1, column=0, sticky="e", padx=(0, 2), pady=(2, 0))
        self.gk_var = tk.IntVar(value=state.gk)
        make_spin(keys, self.gk_var, TRANSPOSE_MIN, TRANSPOSE_MAX,
                  self._on_gk_spin, width=4).grid(row=1, column=1, padx=2, pady=(2, 0))

        pads = tk.Frame(counters)
        pads.grid(row=0, column=1, sticky="nw", padx=(0, 16))
        tk.Label(pads, text="Pad Ch:").grid(row=0, column=0, sticky="e", padx=(0, 2))
        self.gd_var = tk.IntVar(value=state.gd)
        make_spin(pads, self.gd_var, 1, 16, self._on_gd_spin).grid(row=0, column=1, padx=2)
        tk.Label(pads, text="Pad Transpose:").grid(row=1, column=0, sticky="e", padx=(0, 2), pady=(2, 0))
        self.pk_var = tk.IntVar(value=state.pk)
        make_spin(pads, self.pk_var, TRANSPOSE_MIN, TRANSPOSE_MAX,
                  self._on_pk_spin, width=4).grid(row=1, column=1, padx=2, pady=(2, 0))
        self.led_mode_var = tk.StringVar(value="LEDs: Key")
        tk.Label(pads, textvariable=self.led_mode_var, fg="#444").grid(
            row=2, column=0, columnspan=2, sticky="w", pady=(4, 0))

        self.kb_var = tk.IntVar(value=state.knob_bank)
        self.kb_name_vars = [tk.StringVar(value=n) for n in state.knob_bank_names]
        self.kb_name_edit = tk.StringVar(value=state.knob_bank_names[state.knob_bank - 1])
        self.kb_cc_vars = [tk.IntVar(value=cc) for cc in state.knob_ccs[state.knob_bank - 1]]
        gl = list(getattr(state, "knob_ch_global", [True] * 16))
        if len(gl) != 16:
            gl = [True] * 16
        chs = normalize_knob_ch(getattr(state, "knob_ch", None))
        self.kb_ch_global = [tk.BooleanVar(value=bool(g)) for g in gl]
        bank0 = chs[state.knob_bank - 1]
        self.kb_knob_ch_vars = [tk.IntVar(value=int(bank0[i])) for i in range(8)]
        self._kb_shown = state.knob_bank

        knobs = tk.Frame(counters)
        knobs.grid(row=0, column=2, sticky="nw")
        kbhead = tk.Frame(knobs)
        kbhead.grid(row=0, column=0, sticky="w")
        tk.Label(kbhead, text="Knob Bank:").pack(side="left")
        make_spin(kbhead, self.kb_var, 1, 16, self._on_kb_spin).pack(side="left", padx=2)
        name_ent = tk.Entry(kbhead, textvariable=self.kb_name_edit, width=12)
        name_ent.pack(side="left", padx=2)
        name_ent.bind("<Return>", lambda e: self._sync_knob_name_edit())
        name_ent.bind("<FocusOut>", lambda e: self._sync_knob_name_edit())

        ccrow = tk.Frame(knobs)
        ccrow.grid(row=1, column=0, sticky="w", pady=(2, 0))
        chrow = tk.Frame(knobs)
        chrow.grid(row=2, column=0, sticky="w")
        self.kb_ch_spins = []
        for i in range(8):
            col = tk.Frame(ccrow)
            col.pack(side="left", padx=2)
            tk.Label(col, text=f"K{i + 1}", fg="#444").pack(anchor="w")
            sp = ttk.Spinbox(
                col, from_=0, to=127, textvariable=self.kb_cc_vars[i], width=3,
                command=self._sync_knob_ccs,
            )
            sp.pack(anchor="w")
            sp.bind("<Return>", lambda e: self._sync_knob_ccs())
            sp.bind("<FocusOut>", lambda e: self._sync_knob_ccs())
            chcol = tk.Frame(chrow)
            chcol.pack(side="left", padx=2)
            chsp = ttk.Spinbox(
                chcol, from_=1, to=16, textvariable=self.kb_knob_ch_vars[i], width=3,
                command=self._sync_knob_ch,
            )
            chsp.pack(anchor="w")
            chsp.bind("<Return>", lambda e: self._sync_knob_ch())
            chsp.bind("<FocusOut>", lambda e: self._sync_knob_ch())
            self.kb_ch_spins.append(chsp)
        self.kb_top_global = tk.BooleanVar(
            value=bool(state.knob_ch_global[state.knob_bank - 1])
        )
        tk.Checkbutton(
            ccrow, text="Global", variable=self.kb_top_global,
            command=self._on_kb_top_global,
        ).pack(side="left", padx=(8, 0), anchor="s")
        row += 1

        prog_head = tk.Frame(root)
        prog_head.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=(4, 0))
        self._progs_shown = True
        self._prog_toggle = tk.Button(
            prog_head, text="▾  PROG 1–4", command=self._toggle_progs,
            bd=0, highlightthickness=0, takefocus=0, font=("Helvetica", 12, "bold"),
            fg="#333",
        )
        self._prog_toggle.pack(side="left")
        tk.Label(
            prog_head, fg="#666",
            text="click to collapse",
        ).pack(side="left", padx=8)
        row += 1

        progs = ttk.Notebook(root)
        self.progs = progs
        progs.grid(row=row, column=0, columnspan=2, sticky="nw", padx=6, pady=2)
        self._progs_row = row
        row += 1
        self.prog_ui = []
        self._learn_win = None
        self._chord_drag = None
        self._clip_drag = None
        for i in range(4):
            page = ttk.Frame(progs, padding=4)
            progs.add(page, text=f"PROG {i + 1}")
            self._build_prog_tab(page, i)

        log_head = tk.Frame(root)
        log_head.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=(4, 0))
        self._log_shown = True
        self._log_toggle = tk.Button(
            log_head, text="▾  Log", command=self._toggle_log,
            bd=0, highlightthickness=0, takefocus=0, font=("Helvetica", 12, "bold"), fg="#333",
        )
        self._log_toggle.pack(side="left")
        row += 1
        log_row = tk.Frame(root)
        self._log_body = log_row
        log_row.grid(row=row, column=0, columnspan=2, sticky="we", padx=6, pady=2)
        self.log = tk.Text(log_row, height=4, width=80, state="disabled")
        self.log.pack(fill="both", expand=True)
        self._log_row = row
        row += 1

        self.root.grid_columnconfigure(0, weight=0)
        self.root.grid_columnconfigure(1, weight=0)

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.detect_thread = threading.Thread(target=self.detect_mpk_loop, daemon=True)
        self.detect_thread.start()
        self.root.after(50, self._poll_mapper_state)
        self.root.after(8, self._tick_pointer)
        for i in range(4):
            self._show_preset(i)
        self._apply_local_spin_states()
        self.root.after_idle(self._fit_window)
        if IS_WIN:
            self.root.after(250, self._win_midi_hint)

    def _win_midi_hint(self):
        try:
            virt, _default, _extra = self._port_choices()
            if not any(is_loop_name(n) for n in virt):
                self._append_log(
                    "Windows: install loopMIDI, create a port named Minimapper, "
                    "then click Ports and pick it in To DAW."
                )
        except tk.TclError:
            pass

    def _build_prog_tab(self, parent, prog):
        cfg = state.progs[prog]
        ui = {
            "joy_bodies": {},
            "pad_bodies": {},
            "cc_a": tk.IntVar(value=cfg.cc_a),
            "cc_b": tk.IntVar(value=cfg.cc_b),
            "cc_map": [tk.IntVar(value=cfg.cc_map[i]) for i in range(16)],
            "mode": tk.StringVar(value=cfg.pointer_mode),
            "sens": tk.DoubleVar(value=cfg.mouse_sens),
            "cc13_combos": [list(c) for c in cfg.cc13_map],
            "cc13_labels": [],
            "sens_scale": None,
            "chord_map": [list(c) for c in cfg.chord_map],
            "chord_delay": [tk.BooleanVar(value=bool(cfg.chord_delay[i])) for i in range(16)],
            "chord_xpose": [tk.IntVar(value=int(cfg.chord_xpose[i])) for i in range(16)],
            "chord_ch": [tk.IntVar(value=int(cfg.chord_ch[i])) for i in range(16)],
            "chord_ch_global": [tk.BooleanVar(value=bool(cfg.chord_ch_global[i])) for i in range(16)],
            "cc_ch_global": tk.BooleanVar(value=bool(cfg.cc_ch_global)),
            "cc_ch": tk.IntVar(value=int(cfg.cc_ch)),
            "chord_labels": [],
            "chord_label_widgets": [],
            "chord_ch_spins": [],
            "cc_ch_spin": None,
            "kb_pad_labels": [],
            "clip_map": [list(c) for c in cfg.clip_map],
            "clip_delay": [tk.BooleanVar(value=bool(cfg.clip_delay[i])) for i in range(16)],
            "clip_xpose": [tk.IntVar(value=int(cfg.clip_xpose[i])) for i in range(16)],
            "clip_mode": [tk.StringVar(value="One-shot" if cfg.clip_mode[i] == "one-shot"
                                       else "Continuous") for i in range(16)],
            "clip_overdub": tk.BooleanVar(value=bool(state.clip_overdub[prog])),
            "clip_labels": [],
            "clip_label_widgets": [],
        }
        ui["joy_var"] = tk.StringVar(value=JOY_LABELS.get(cfg.joy_preset, JOY_LABELS[DEFAULT_JOY[prog]]))
        ui["pad_var"] = tk.StringVar(value=PAD_LABELS.get(cfg.pad_preset, PAD_LABELS[DEFAULT_PAD[prog]]))

        head = tk.Frame(parent)
        head.grid(row=0, column=0, sticky="w", pady=(0, 3))
        tk.Label(head, text="Joystick:").pack(side="left", padx=(0, 4))
        jcb = ttk.Combobox(
            head, textvariable=ui["joy_var"], width=20, state="readonly",
            values=[lab for _k, lab in JOY_CHOICES],
        )
        jcb.pack(side="left")
        jcb.bind("<<ComboboxSelected>>", lambda _e, p=prog: self._on_preset(p))
        tk.Label(head, text="Pads:").pack(side="left", padx=(12, 4))
        pcb = ttk.Combobox(
            head, textvariable=ui["pad_var"], width=20, state="readonly",
            values=[lab for _k, lab in PAD_CHOICES],
        )
        pcb.pack(side="left")
        pcb.bind("<<ComboboxSelected>>", lambda _e, p=prog: self._on_preset(p))
        tools = tk.Frame(head)
        tools.pack(side="left", padx=(14, 0))
        tk.Button(tools, text="Save…",
                  command=lambda p=prog: self._save_chord_patch(p)).pack(side="left", padx=(0, 3))
        tk.Button(tools, text="Load…",
                  command=lambda p=prog: self._load_chord_patch(p)).pack(side="left", padx=3)
        tk.Button(tools, text="MIDI…",
                  command=lambda p=prog: self._export_chord_midi(p)).pack(side="left", padx=3)
        ui["chord_tools"] = tools
        tools.pack_forget()
        clip_tools = tk.Frame(head)
        tk.Checkbutton(
            clip_tools, text="Overdub", variable=ui["clip_overdub"],
            command=lambda p=prog: self._sync_clip_overdub(p),
        ).pack(side="left", padx=(0, 8))
        tk.Button(clip_tools, text="Save…",
                  command=lambda p=prog: self._save_clip_patch(p)).pack(side="left", padx=(0, 3))
        tk.Button(clip_tools, text="Load…",
                  command=lambda p=prog: self._load_clip_patch(p)).pack(side="left", padx=3)
        ui["clip_tools"] = clip_tools
        clip_tools.pack_forget()

        joy_host = tk.Frame(parent)
        joy_host.grid(row=1, column=0, sticky="nw")
        pad_host = tk.Frame(parent)
        pad_host.grid(row=2, column=0, sticky="nsew")
        parent.grid_columnconfigure(0, weight=1)
        parent.grid_rowconfigure(2, weight=1)

        # --- Joystick: MW/PB + Custom CCs ---
        joy_mw = tk.Frame(joy_host)
        tk.Label(
            joy_mw, text="Joystick Down/Up remapped onto Key Channel. PB + MW pass through.",
            fg="#666",
        ).grid(row=0, column=0, columnspan=4, sticky="w")
        tk.Label(joy_mw, text="Joystick Down →").grid(row=1, column=0, padx=4, pady=2, sticky="e")
        sp_a = ttk.Spinbox(joy_mw, from_=0, to=127, textvariable=ui["cc_a"], width=5,
                           command=lambda p=prog: self._sync_mw(p))
        sp_a.grid(row=1, column=1, padx=2, sticky="w")
        sp_a.bind("<Return>", lambda e, p=prog: self._sync_mw(p))
        sp_a.bind("<FocusOut>", lambda e, p=prog: self._sync_mw(p))
        tk.Label(joy_mw, text="Joystick Up →").grid(row=1, column=2, padx=4, sticky="e")
        sp_b = ttk.Spinbox(joy_mw, from_=0, to=127, textvariable=ui["cc_b"], width=5,
                           command=lambda p=prog: self._sync_mw(p))
        sp_b.grid(row=1, column=3, padx=2, sticky="w")
        sp_b.bind("<Return>", lambda e, p=prog: self._sync_mw(p))
        sp_b.bind("<FocusOut>", lambda e, p=prog: self._sync_mw(p))
        ui["joy_bodies"][PRESET_MW] = joy_mw

        joy_ptr = tk.Frame(joy_host)
        tk.Label(joy_ptr, text="Joystick pointing only (PB = X, no MIDI out).",
                 fg="#666").grid(row=0, column=0, columnspan=4, sticky="w")
        ttk.Radiobutton(
            joy_ptr, text="Mouse", variable=ui["mode"], value="mouse",
            command=lambda p=prog: self._sync_pointer(p),
        ).grid(row=1, column=0, padx=4, sticky="w")
        ttk.Radiobutton(
            joy_ptr, text="D-Pad", variable=ui["mode"], value="dpad",
            command=lambda p=prog: self._sync_pointer(p),
        ).grid(row=1, column=1, padx=4, sticky="w")
        tk.Label(joy_ptr, text="Sens:").grid(row=1, column=2, sticky="e")
        scale = ttk.Scale(
            joy_ptr, from_=1, to=20, variable=ui["sens"], orient="horizontal",
            command=lambda _v, p=prog: self._sync_pointer(p),
        )
        scale.grid(row=1, column=3, sticky="we", padx=4)
        ui["sens_scale"] = scale
        ui["joy_bodies"][PRESET_PTR] = joy_ptr

        joy_key = tk.Frame(joy_host)
        tk.Label(joy_key, text="Joystick Down/Up = Key Transpose. Pitchbend passes on Key Channel.",
                 fg="#666").pack(anchor="w")
        ui["joy_bodies"][PRESET_KEY] = joy_key

        joy_pad = tk.Frame(joy_host)
        tk.Label(joy_pad, text="Joystick Down/Up = Pad Transpose. Pitchbend passes on Key Channel.",
                 fg="#666").pack(anchor="w")
        ui["joy_bodies"][PRESET_PAD] = joy_pad

        joy_kch = tk.Frame(joy_host)
        tk.Label(joy_kch, text="Joystick Down/Up = Key Channel. Pitchbend passes on Key Channel.",
                 fg="#666").pack(anchor="w")
        ui["joy_bodies"][PRESET_KEY_CH] = joy_kch

        joy_pch = tk.Frame(joy_host)
        tk.Label(joy_pch, text="Joystick Down/Up = Pad Channel. Pitchbend passes on Key Channel.",
                 fg="#666").pack(anchor="w")
        ui["joy_bodies"][PRESET_PAD_CH] = joy_pch

        joy_pb = tk.Frame(joy_host)
        tk.Label(joy_pb, text="Pitchbend passes on Key Channel. Joystick CCs ignored.",
                 fg="#666").pack(anchor="w")
        ui["joy_bodies"][PRESET_PB] = joy_pb

        # --- Pads: Custom CCs ---
        pad_mw = tk.Frame(pad_host)
        mw_head = tk.Frame(pad_mw)
        mw_head.grid(row=0, column=0, sticky="w", pady=(0, 2))
        tk.Label(mw_head, text="Pads remap CCs.  Output:").pack(side="left")
        tk.Checkbutton(
            mw_head, text="Global", variable=ui["cc_ch_global"],
            command=lambda p=prog: self._sync_cc_route(p),
        ).pack(side="left")
        tk.Label(mw_head, text="Ch").pack(side="left", padx=(8, 2))
        sp_ch = ttk.Spinbox(
            mw_head, from_=1, to=16, textvariable=ui["cc_ch"], width=3,
            command=lambda p=prog: self._sync_cc_route(p),
        )
        sp_ch.pack(side="left")
        sp_ch.bind("<Return>", lambda e, p=prog: self._sync_cc_route(p))
        sp_ch.bind("<FocusOut>", lambda e, p=prog: self._sync_cc_route(p))
        ui["cc_ch_spin"] = sp_ch
        grid = tk.Frame(pad_mw)
        grid.grid(row=1, column=0, sticky="w")
        for i in range(16):
            r, c = divmod(i, 4)
            cell = tk.Frame(grid)
            cell.grid(row=(3 - r), column=c, padx=2, pady=1, sticky="w")
            tk.Label(cell, text=f"Pad {i + 1}", width=6, anchor="e").pack(side="left")
            sp = ttk.Spinbox(cell, from_=0, to=127, textvariable=ui["cc_map"][i], width=3,
                             command=lambda p=prog: self._sync_cc_map(p))
            sp.pack(side="left")
            sp.bind("<Return>", lambda e, p=prog: self._sync_cc_map(p))
            sp.bind("<FocusOut>", lambda e, p=prog: self._sync_cc_map(p))
        ui["pad_bodies"][PRESET_MW] = pad_mw

        pad_key = tk.Frame(pad_host)
        tk.Label(pad_key, text="Pads select Key Channel (release ignored).",
                 fg="#666").pack(anchor="w")
        ui["pad_bodies"][PRESET_KEY] = pad_key

        pad_pad = tk.Frame(pad_host)
        tk.Label(pad_pad, text="Pads select Pad Channel (LEDs follow).",
                 fg="#666").pack(anchor="w")
        ui["pad_bodies"][PRESET_PAD] = pad_pad

        pad_ptr = tk.Frame(pad_host)
        tk.Label(pad_ptr, text="Pads = keys/clicks. Combos tap; single holds.",
                 fg="#666").grid(row=0, column=0, sticky="w")
        keys = tk.Frame(pad_ptr)
        keys.grid(row=1, column=0, sticky="w")
        for i in range(16):
            r, c = divmod(i, 4)
            cell = tk.Frame(keys)
            cell.grid(row=(3 - r), column=c, padx=2, pady=1, sticky="w")
            tk.Label(cell, text=f"Pad {i + 1}", width=6, anchor="e").pack(side="left")
            var = tk.StringVar(value=format_combo(cfg.cc13_map[i]))
            tk.Label(cell, textvariable=var, width=12, relief="groove",
                     anchor="w").pack(side="left", padx=(0, 1))
            tk.Button(cell, text="Learn", width=4,
                      command=lambda s=i, p=prog: self._learn_cc13(p, s)).pack(side="left")
            tk.Button(cell, text="×", width=1,
                      command=lambda s=i, p=prog: self._set_cc13(p, s, [])).pack(side="left")
            ui["cc13_labels"].append(var)
        ui["pad_bodies"][PRESET_PTR] = pad_ptr

        knb = tk.Frame(pad_host)
        tk.Label(
            knb,
            text="Pads select Knob Bank. Drag to swap · Option-drag to copy.",
            fg="#666",
        ).grid(row=0, column=0, sticky="w")
        kbgrid = tk.Frame(knb)
        kbgrid.grid(row=1, column=0, sticky="w")
        for i in range(16):
            r, c = divmod(i, 4)
            cell = tk.Frame(kbgrid, relief="groove", bd=1)
            cell.grid(row=(3 - r), column=c, padx=2, pady=1, sticky="w")
            top = tk.Frame(cell)
            top.pack(anchor="w")
            lab = tk.Label(top, text=f"Pad {i + 1}", width=6, anchor="e", cursor="hand2")
            lab.pack(side="left")
            ent = tk.Entry(top, textvariable=self.kb_name_vars[i], width=10)
            ent.pack(side="left")
            ent.bind("<Return>", lambda e: self._sync_knob_names())
            ent.bind("<FocusOut>", lambda e: self._sync_knob_names())
            bot = tk.Frame(cell)
            bot.pack(anchor="w")
            tk.Checkbutton(
                bot, text="Global", variable=self.kb_ch_global[i],
                command=self._on_kb_pad_global,
            ).pack(side="left")
            lab._kb_ref = i
            cell._kb_ref = i
            ent._kb_ref = i
            lab.bind("<ButtonPress-1>", lambda e, s=i: self._kb_press(s, e))
            lab.bind("<ButtonRelease-1>", self._kb_release)
            ui["kb_pad_labels"].append(lab)
        ui["pad_bodies"][PRESET_KNOB] = knb

        chd = tk.Frame(pad_host)
        tk.Label(
            chd,
            text="Program Change = Learn. Pads play chords (empty = Learn).  "
                 "Drag swap · Option-drag copy.",
            fg="#666", wraplength=640, justify="left",
        ).grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 2))
        chords = tk.Frame(chd)
        chords.grid(row=1, column=0, columnspan=4, sticky="w")
        for i in range(16):
            r, c = divmod(i, 4)
            cell = tk.Frame(chords)
            cell.grid(row=(3 - r), column=c, padx=1, pady=1, sticky="nw")
            top = tk.Frame(cell)
            top.pack(anchor="w")
            tk.Label(top, text=f"Pad {i + 1}", width=5, anchor="e").pack(side="left")
            var = tk.StringVar(value=format_chord(cfg.chord_map[i], cfg.chord_xpose[i]))
            spin = ChordNameSpin(
                top, var, ui["chord_xpose"][i],
                on_xpose=lambda p=prog, s=i: self._on_chord_xpose(p, s),
                on_clear=lambda s=i, p=prog: self._set_chord(p, s, []),
                prog=prog, slot=i, gui=self,
            )
            spin.pack(side="left")
            lab = spin._lab
            cell._chord_ref = (prog, i)
            bot = tk.Frame(cell)
            bot.pack(anchor="w")
            tk.Label(bot, text="Ch", width=5, anchor="e").pack(side="left")
            chsp = make_spin(
                bot, ui["chord_ch"][i], 1, 16,
                lambda p=prog: self._sync_chords(p),
            )
            chsp.pack(side="left")
            ui["chord_ch_spins"].append(chsp)
            tk.Checkbutton(
                bot, text="Global", variable=ui["chord_ch_global"][i],
                command=lambda p=prog: self._sync_chords(p),
            ).pack(side="left")
            tk.Checkbutton(
                bot, text="Roll", variable=ui["chord_delay"][i],
                command=lambda p=prog: self._sync_chords(p),
            ).pack(side="left")
            ui["chord_labels"].append(var)
            ui["chord_label_widgets"].append(lab)
        ui["pad_bodies"][PRESET_CHORD] = chd

        clipf = tk.Frame(pad_host)
        tk.Label(
            clipf,
            text="CC 0–15 = Learn (or Overdub). Program Change 0–15 = clear.  "
                 "Empty pads silent. Independent of Key Ch / transpose.  "
                 "Drag swap · Option-drag copy.",
            fg="#666", wraplength=640, justify="left",
        ).grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 2))
        clips = tk.Frame(clipf)
        clips.grid(row=1, column=0, columnspan=4, sticky="w")
        for i in range(16):
            r, c = divmod(i, 4)
            cell = tk.Frame(clips)
            cell.grid(row=(3 - r), column=c, padx=1, pady=1, sticky="nw")
            top = tk.Frame(cell)
            top.pack(anchor="w")
            tk.Label(top, text=f"Pad {i + 1}", width=5, anchor="e").pack(side="left")
            var = tk.StringVar(value=format_clip(cfg.clip_map[i], cfg.clip_xpose[i]))
            spin = ChordNameSpin(
                top, var, ui["clip_xpose"][i],
                on_xpose=lambda p=prog, s=i: self._on_clip_xpose(p, s),
                on_clear=lambda s=i, p=prog: self._set_clip(p, s, []),
                prog=prog, slot=i, gui=self, kind="clip",
            )
            spin.pack(side="left")
            lab = spin._lab
            cell._clip_ref = (prog, i)
            bot = tk.Frame(cell)
            bot.pack(anchor="w")
            tk.Label(bot, text="", width=5).pack(side="left")
            tk.Checkbutton(
                bot, text="Roll", variable=ui["clip_delay"][i],
                command=lambda p=prog: self._sync_clips(p),
            ).pack(side="left")
            mode = ttk.Combobox(
                bot, textvariable=ui["clip_mode"][i],
                values=("Continuous", "One-shot"), width=10, state="readonly",
            )
            mode.pack(side="left", padx=(4, 0))
            mode.bind("<<ComboboxSelected>>", lambda e, p=prog: self._sync_clips(p))
            ui["clip_labels"].append(var)
            ui["clip_label_widgets"].append(lab)
        ui["pad_bodies"][PRESET_CLIP] = clipf

        self.prog_ui.append(ui)
        for frame in list(ui["joy_bodies"].values()) + list(ui["pad_bodies"].values()):
            frame.grid(row=0, column=0, sticky="nsew")

    def _toggle_progs(self):
        self._progs_shown = not self._progs_shown
        if self._progs_shown:
            self.progs.grid()
            self._prog_toggle.config(text="▾  PROG 1–4")
        else:
            self.progs.grid_remove()
            self._prog_toggle.config(text="▸  PROG 1–4")
        self._fit_window()

    def _toggle_io(self):
        self._io_shown = not self._io_shown
        if self._io_shown:
            self._io_body.grid()
            self._io_toggle.config(text="▾  I/O")
        else:
            self._io_body.grid_remove()
            self._io_toggle.config(text="▸  I/O")
        self._fit_window()

    def _toggle_global(self):
        self._glob_shown = not self._glob_shown
        if self._glob_shown:
            self._glob_body.grid()
            self._glob_toggle.config(text="▾  Global")
        else:
            self._glob_body.grid_remove()
            self._glob_toggle.config(text="▸  Global")
        self._fit_window()

    def _toggle_log(self):
        self._log_shown = not self._log_shown
        if self._log_shown:
            self._log_body.grid()
            self._log_toggle.config(text="▾  Log")
        else:
            self._log_body.grid_remove()
            self._log_toggle.config(text="▸  Log")
        self._fit_window()

    def _fit_window(self):
        self.root.minsize(1, 1)
        self.root.grid_rowconfigure(self._progs_row, weight=0)
        self.root.update_idletasks()
        req_w = max(1, self.root.winfo_reqwidth())
        req_h = max(1, self.root.winfo_reqheight())
        self.root.geometry(f"{req_w}x{req_h}")
        self.root.minsize(req_w, req_h)

    def _on_preset(self, prog):
        self._sync_mw(prog)
        self._sync_cc_map(prog)
        self._sync_cc13(prog)
        self._sync_pointer(prog)
        self._sync_chords(prog)
        self._sync_clips(prog)
        self._sync_clip_overdub(prog)
        self._sync_cc_route(prog)
        self._sync_knob_names()
        self._sync_knob_ccs()
        self._sync_knob_ch()
        self._show_preset(prog)
        self._apply_local_spin_states()

    def _show_preset(self, prog):
        ui = self.prog_ui[prog]
        joy = JOY_BY_LABEL.get(ui["joy_var"].get(), DEFAULT_JOY[prog])
        pad = PAD_BY_LABEL.get(ui["pad_var"].get(), DEFAULT_PAD[prog])
        with state.lock:
            state.progs[prog].joy_preset = joy
            state.progs[prog].pad_preset = pad
        for k, frame in ui["joy_bodies"].items():
            if k == joy:
                frame.grid(row=0, column=0, sticky="nsew")
            else:
                frame.grid_remove()
        for k, frame in ui["pad_bodies"].items():
            if k == pad:
                frame.grid(row=0, column=0, sticky="nsew")
            else:
                frame.grid_remove()
        tools = ui.get("chord_tools")
        if tools is not None:
            if pad == PRESET_CHORD:
                tools.pack(side="left", padx=(14, 0))
            else:
                tools.pack_forget()
        ctools = ui.get("clip_tools")
        if ctools is not None:
            if pad == PRESET_CLIP:
                ctools.pack(side="left", padx=(14, 0))
            else:
                ctools.pack_forget()

    def _port_choices(self):
        outs = [n for n in list_midi_outputs() if not is_mpk_name(n)]
        extra = ["None"] + outs
        virt = []
        if IS_MAC:
            virt.append(VIRT_CREATE)
        virt.extend(outs)
        if not virt:
            virt = ["None"]
        preferred = next((n for n in virt if is_loop_name(n)), None)
        if IS_MAC:
            default = VIRT_CREATE
        else:
            default = preferred or (outs[0] if outs else "None")
        return virt, default, extra

    def _hid_hint(self, available):
        if available:
            if IS_WIN:
                return "Keys/clicks ready (SendInput)."
            return (
                "Keys/clicks ready. On Mac: System Settings → Privacy & Security → "
                "Accessibility → allow Python (or Terminal)."
            )
        err = f" ({self.hid._error})" if getattr(self.hid, "_error", None) else ""
        if IS_WIN:
            return f"Keys/clicks unavailable{err}."
        return (
            f"Keys/clicks unavailable{err}. On Mac, allow Python in Accessibility."
        )

    def detect_mpk_loop(self):
        # Do not enumerate MIDI ports while the filter holds them —
        # opening a hidden MidiIn to list names can crash rtmidi.
        while True:
            if self.filter is not None:
                time.sleep(1.0)
                continue
            try:
                ports = list_midi_inputs() + list_midi_outputs()
                present = any(is_mpk_name(n) for n in ports)
            except Exception:
                present = False
            try:
                self.root.after(0, self.update_status_indicator, present)
            except Exception:
                break
            time.sleep(1.0)

    def update_status_indicator(self, connected):
        self.mpk_status_var.set("Connected" if connected else "Disconnected")
        self.mpk_status_label.config(fg="green" if connected else "red")

    def refresh_ports(self):
        virt_vals, virt_default, extra_vals = self._port_choices()
        self.virt_out_combo["values"] = virt_vals
        self.daw_out_combo["values"] = extra_vals
        if self.virt_out_var.get() not in virt_vals:
            self.virt_out_var.set(virt_default)
        if self.daw_out_var.get() not in extra_vals:
            self.daw_out_var.set("None")
        self._append_log("Ports refreshed.")

    def _on_state_change(self, gc_val, gk_val, gd_val, pk_val, blink_high):
        # Unused: counters are copied on the Tk thread by _poll_mapper_state.
        return

    def _poll_mapper_state(self):
        try:
            with state.lock:
                snap = (state.gc, state.gk, state.gd, state.pk, state.led_mode,
                        state.knob_bank, state.chord_learn)
            if snap != self._last_ui:
                new_bank = int(snap[5])
                if new_bank != self._kb_shown:
                    self._sync_knob_ccs()
                    self._sync_knob_names()
                self._syncing = True
                try:
                    self.gc_var.set(int(snap[0]))
                    self.gk_var.set(int(snap[1]))
                    self.gd_var.set(int(snap[2]))
                    self.pk_var.set(int(snap[3]))
                    if snap[4] == "learn" and snap[6] is not None:
                        self.led_mode_var.set(f"LEDs: Learn pad {int(snap[6][1]) + 1}")
                    elif snap[4] == "pad":
                        self.led_mode_var.set("LEDs: Pad Channel")
                    else:
                        self.led_mode_var.set("LEDs: Key Channel")
                    if new_bank != self._kb_shown:
                        self._load_knob_editor(new_bank)
                    self.kb_var.set(new_bank)
                    try:
                        self.kb_name_edit.set(self.kb_name_vars[new_bank - 1].get())
                    except (tk.TclError, IndexError):
                        pass
                finally:
                    self._syncing = False
                self._last_ui = snap
        except tk.TclError:
            return
        self.root.after(50, self._poll_mapper_state)

    def _flush_input_events(self):
        while True:
            try:
                combo, kind = input_events.get_nowait()
            except queue.Empty:
                break
            combo = parse_combo(combo)
            if not combo:
                continue
            if kind is True:
                kind = "down"
            elif kind is False:
                kind = "up"
            if not self.hid.available():
                if not self._hid_warned:
                    self._hid_warned = True
                    self._append_log(self._hid_hint(False))
                continue
            if kind == "tap":
                self.hid.tap(combo)
            elif kind == "down":
                for action in combo:
                    self.hid.send(action, True)
            else:
                for action in reversed(combo):
                    self.hid.send(action, False)

    def _set_dpad(self, direction):
        if direction == self._dpad_held:
            return
        if self._dpad_held:
            if self.hid.available():
                self.hid.send(self._dpad_held, False)
        self._dpad_held = direction
        if direction:
            if self.hid.available():
                self.hid.send(direction, True)
            elif not self._hid_warned:
                self._hid_warned = True
                self._append_log(self._hid_hint(False))

    def _tick_pointer(self):
        """Apply Channel 4 mouse / D-Pad and queued keystrokes on the Tk thread only."""
        try:
            self._flush_input_events()
            with state.lock:
                ax, ay = state.axis_x, state.axis_y
                pidx = state.pointer_prog
                cfg = state.progs[pidx]
                if cfg.joy_preset != PRESET_PTR:
                    cfg = next((p for p in state.progs if p.joy_preset == PRESET_PTR), None)
                if cfg is None:
                    mode = None
                    sens = 0.0
                else:
                    mode = cfg.pointer_mode
                    sens = cfg.mouse_sens
            if not mode:
                self._set_dpad(None)
            elif mode == "dpad":
                direction = None
                if abs(ax) > abs(ay) and abs(ax) > DPAD_THRESHOLD:
                    direction = "arrow right" if ax > 0 else "arrow left"
                elif abs(ay) > DPAD_THRESHOLD:
                    # axis_y is already inverted (MIDI up → negative screen Y → arrow up)
                    direction = "arrow up" if ay < 0 else "arrow down"
                if self.filter:
                    self._set_dpad(direction)
                else:
                    self._set_dpad(None)
            else:
                self._set_dpad(None)
                vx = (ax * abs(ax)) * sens
                vy = (ay * abs(ay)) * sens
                self._frac_x += vx
                self._frac_y += vy
                ix = int(self._frac_x)
                iy = int(self._frac_y)
                self._frac_x -= ix
                self._frac_y -= iy
                if (ix or iy) and self.filter:
                    if self.pointer.available():
                        self.pointer.move(ix, iy, self.hid.held_mouse())
                    elif not self._pointer_warned:
                        self._pointer_warned = True
                        self._append_log("Pointer: no mouse backend on this system.")
        except tk.TclError:
            return
        self.root.after(8, self._tick_pointer)

    def _append_log(self, text):
        def do_log():
            self.log.configure(state="normal")
            self.log.insert("end", text + "\n")
            self.log.see("end")
            self.log.configure(state="disabled")
        self.root.after(0, do_log)

    def _sync_mw(self, prog):
        ui = self.prog_ui[prog]
        try:
            a = int(ui["cc_a"].get())
            b = int(ui["cc_b"].get())
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.progs[prog].cc_a = clamp(a, 0, 127)
            state.progs[prog].cc_b = clamp(b, 0, 127)

    def _sync_cc_map(self, prog):
        mapping = []
        for var in self.prog_ui[prog]["cc_map"]:
            try:
                mapping.append(clamp(int(var.get()), 0, 127))
            except (tk.TclError, ValueError):
                mapping.append(0)
        with state.lock:
            state.progs[prog].cc_map = mapping

    def _set_cc13(self, prog, slot, combo):
        combo = parse_combo(combo)
        ui = self.prog_ui[prog]
        ui["cc13_combos"][slot] = combo
        if slot < len(ui["cc13_labels"]):
            ui["cc13_labels"][slot].set(format_combo(combo))
        with state.lock:
            state.progs[prog].cc13_map[slot] = list(combo)

    def _sync_cc13(self, prog=None):
        progs = range(4) if prog is None else (prog,)
        with state.lock:
            for p in progs:
                state.progs[p].cc13_map = [
                    list(parse_combo(c)) for c in self.prog_ui[p]["cc13_combos"]
                ]

    def _sync_pointer(self, prog):
        ui = self.prog_ui[prog]
        try:
            sens = float(ui["sens"].get())
        except (tk.TclError, ValueError):
            return
        mode = ui["mode"].get()
        with state.lock:
            state.progs[prog].pointer_mode = mode
            state.progs[prog].mouse_sens = clamp(sens, 1.0, 20.0)
        try:
            ui["sens_scale"].state(["disabled"] if mode == "dpad" else ["!disabled"])
        except Exception:
            pass

    def _sync_all_progs(self):
        if not getattr(self, "prog_ui", None):
            return
        n = min(4, len(self.prog_ui))
        for p in range(n):
            self._sync_mw(p)
            self._sync_cc_map(p)
            self._sync_cc13(p)
            self._sync_pointer(p)
            self._sync_chords(p)
            self._sync_clips(p)
            self._sync_clip_overdub(p)
            self._sync_cc_route(p)
        self._sync_knob_names()
        self._sync_knob_ccs()
        self._sync_knob_ch()

    def _learn_cc13(self, prog, slot):
        if self._learn_win is not None:
            try:
                self._learn_win.destroy()
            except tk.TclError:
                pass
            self._learn_win = None

        win = tk.Toplevel(self.root)
        self._learn_win = win
        win.title(f"Learn CC{slot:02d}")
        win.transient(self.root)
        win.resizable(False, False)
        tk.Label(
            win,
            text=f"CC{slot:02d} — hold the combo, then release all keys.\n"
                 "Esc cancels. Mouse: hold to click/drag, or pick a double-click.",
            justify="left",
        ).pack(padx=16, pady=(12, 6))
        status = tk.StringVar(value="listening…")
        tk.Label(win, textvariable=status, width=32, relief="groove").pack(padx=16, pady=4)

        btns = tk.Frame(win)
        btns.pack(pady=8)
        for label, combo in (
            ("Mouse Left", ["mouse left"]),
            ("Mouse Right", ["mouse right"]),
            ("Mouse Middle", ["mouse middle"]),
        ):
            tk.Button(
                btns, text=label,
                command=lambda c=combo, p=prog: self._finish_learn(p, slot, c, win),
            ).pack(side="left", padx=4)
        dbl = tk.Frame(win)
        dbl.pack(pady=(0, 8))
        for label, combo in (
            ("Left Double", ["mouse left double"]),
            ("Right Double", ["mouse right double"]),
            ("Middle Double", ["mouse middle double"]),
        ):
            tk.Button(
                dbl, text=label,
                command=lambda c=combo, p=prog: self._finish_learn(p, slot, c, win),
            ).pack(side="left", padx=4)
        tk.Button(win, text="Cancel", command=win.destroy).pack(pady=(0, 10))

        held = []
        chord = []

        def key_down(event):
            keysym = (event.keysym or "").lower()
            if keysym == "escape" and not held:
                win.destroy()
                return "break"
            action = tk_event_to_action(event)
            if action and action not in held:
                held.append(action)
                chord[:] = list(held)
                status.set("+".join(normalize_combo(chord)) or "listening…")
            return "break"

        def key_up(event):
            action = tk_event_to_action(event)
            if action in held:
                held.remove(action)
            if not held and chord:
                self._finish_learn(prog, slot, chord, win)
            return "break"

        win.bind("<KeyPress>", key_down)
        win.bind("<KeyRelease>", key_up)
        win.protocol("WM_DELETE_WINDOW", win.destroy)

        def _ready():
            try:
                win.grab_set()
                win.focus_force()
            except tk.TclError:
                pass

        win.after(50, _ready)

    def _finish_learn(self, prog, slot, combo, win):
        self._set_cc13(prog, slot, combo)
        self._append_log(
            f"PROG{prog + 1} CC{slot:02d} learned → {format_combo(parse_combo(combo))}"
        )
        try:
            win.destroy()
        except tk.TclError:
            pass
        if self._learn_win is win:
            self._learn_win = None

    def _on_gc_spin(self):
        if self._syncing:
            return
        try:
            val = int(self.gc_var.get())
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.gc = clamp(val, 1, 16)
            state.blink_high = state.gc > 8

    def _on_gd_spin(self):
        if self._syncing:
            return
        try:
            val = int(self.gd_var.get())
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.gd = clamp(val, 1, 16)
            state.led_mode = "pad"

    def _on_gk_spin(self):
        if self._syncing:
            return
        try:
            val = int(self.gk_var.get())
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.gk = clamp(val, TRANSPOSE_MIN, TRANSPOSE_MAX)

    def _on_pk_spin(self):
        if self._syncing:
            return
        try:
            val = int(self.pk_var.get())
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.pk = clamp(val, TRANSPOSE_MIN, TRANSPOSE_MAX)

    def _on_kb_spin(self):
        if self._syncing:
            return
        try:
            val = int(self.kb_var.get())
        except (tk.TclError, ValueError):
            return
        val = clamp(val, 1, 16)
        self._sync_knob_ccs()
        with state.lock:
            state.knob_bank = val
        self._load_knob_editor(val)

    def _sync_knob_name_edit(self):
        if self._syncing:
            return
        try:
            name = (self.kb_name_edit.get() or "").strip() or f"Bank {self._kb_shown}"
        except tk.TclError:
            return
        idx = clamp(self._kb_shown, 1, 16) - 1
        was = self._syncing
        self._syncing = True
        try:
            self.kb_name_vars[idx].set(name)
        finally:
            self._syncing = was
        self._sync_knob_names()

    def _sync_knob_names(self):
        if self._syncing:
            return
        names = []
        for i, var in enumerate(self.kb_name_vars):
            try:
                names.append((var.get() or "").strip() or f"Bank {i + 1}")
            except tk.TclError:
                names.append(f"Bank {i + 1}")
        with state.lock:
            state.knob_bank_names = names
        try:
            self.kb_name_edit.set(names[clamp(self._kb_shown, 1, 16) - 1])
        except tk.TclError:
            pass

    def _spin_enable(self, sp, on):
        if sp is None:
            return
        try:
            if on:
                sp.state(["!disabled"])
            else:
                sp.state(["disabled"])
        except tk.TclError:
            try:
                sp.configure(state="normal" if on else "disabled")
            except tk.TclError:
                pass

    def _apply_local_spin_states(self):
        glob_on = bool(self.kb_top_global.get()) if hasattr(self, "kb_top_global") else True
        for sp in getattr(self, "kb_ch_spins", []):
            self._spin_enable(sp, not glob_on)
        for ui in getattr(self, "prog_ui", []):
            self._spin_enable(ui.get("cc_ch_spin"), not bool(ui["cc_ch_global"].get()))
            spins = ui.get("chord_ch_spins") or []
            gls = ui.get("chord_ch_global") or []
            for i, sp in enumerate(spins):
                self._spin_enable(sp, not bool(gls[i].get()))

    def _on_kb_pad_global(self):
        self._sync_knob_ch()

    def _sync_knob_ch(self):
        if self._syncing:
            return
        gl = [bool(v.get()) for v in self.kb_ch_global]
        row = []
        for v in self.kb_knob_ch_vars:
            try:
                row.append(clamp(int(v.get()), 1, 16))
            except (tk.TclError, ValueError):
                row.append(1)
        bank = clamp(self._kb_shown, 1, 16) - 1
        with state.lock:
            chs = normalize_knob_ch(state.knob_ch)
            chs[bank] = row
            state.knob_ch_global = gl
            state.knob_ch = chs
        try:
            if bool(self.kb_top_global.get()) != gl[bank]:
                was = self._syncing
                self._syncing = True
                try:
                    self.kb_top_global.set(gl[bank])
                finally:
                    self._syncing = was
        except (tk.TclError, AttributeError):
            pass
        self._apply_local_spin_states()

    def _on_kb_top_global(self):
        if self._syncing:
            return
        idx = clamp(self._kb_shown, 1, 16) - 1
        val = bool(self.kb_top_global.get())
        try:
            self.kb_ch_global[idx].set(val)
        except tk.TclError:
            pass
        self._sync_knob_ch()
        self._apply_local_spin_states()

    def _sync_cc_route(self, prog):
        ui = self.prog_ui[prog]
        try:
            ch = clamp(int(ui["cc_ch"].get()), 1, 16)
        except (tk.TclError, ValueError):
            ch = 10
        with state.lock:
            state.progs[prog].cc_ch_global = bool(ui["cc_ch_global"].get())
            state.progs[prog].cc_ch = ch
        self._apply_local_spin_states()

    def _sync_knob_ccs(self):
        if self._syncing:
            return
        mapping = []
        for var in self.kb_cc_vars:
            try:
                mapping.append(clamp(int(var.get()), 0, 127))
            except (tk.TclError, ValueError):
                mapping.append(0)
        bank = clamp(self._kb_shown, 1, 16) - 1
        with state.lock:
            state.knob_ccs[bank] = mapping

    def _load_knob_editor(self, bank):
        bank = clamp(int(bank), 1, 16)
        with state.lock:
            ccs = list(state.knob_ccs[bank - 1])
            names = list(state.knob_bank_names)
            gl = list(state.knob_ch_global)
            chs = normalize_knob_ch(state.knob_ch)
        was = self._syncing
        self._syncing = True
        try:
            for i, cc in enumerate(ccs):
                self.kb_cc_vars[i].set(int(cc))
            if self.kb_name_vars[bank - 1].get() != names[bank - 1]:
                self.kb_name_vars[bank - 1].set(names[bank - 1])
            self.kb_name_edit.set(names[bank - 1])
            for i in range(16):
                self.kb_ch_global[i].set(bool(gl[i]))
            row = chs[bank - 1]
            for i in range(8):
                self.kb_knob_ch_vars[i].set(int(row[i]))
            self.kb_top_global.set(bool(gl[bank - 1]))
            self._kb_shown = bank
        finally:
            self._syncing = was
        self._apply_local_spin_states()

    def _set_chord(self, prog, slot, notes):
        notes = parse_chord(notes)
        ui = self.prog_ui[prog]
        ui["chord_map"][slot] = notes
        self._refresh_chord_label(prog, slot)
        with state.lock:
            state.progs[prog].chord_map[slot] = [dict(e) for e in notes]

    def _refresh_chord_label(self, prog, slot):
        ui = self.prog_ui[prog]
        try:
            xp = int(ui["chord_xpose"][slot].get())
        except (tk.TclError, ValueError, KeyError):
            xp = 0
        if slot < len(ui["chord_labels"]):
            ui["chord_labels"][slot].set(format_chord(ui["chord_map"][slot], xpose=xp))

    def _on_chord_xpose(self, prog, slot):
        if self._syncing:
            return
        try:
            xp = clamp(int(self.prog_ui[prog]["chord_xpose"][slot].get()),
                       TRANSPOSE_MIN, TRANSPOSE_MAX)
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.progs[prog].chord_xpose[slot] = xp
        self._refresh_chord_label(prog, slot)

    def _sync_chords(self, prog=None):
        progs = range(4) if prog is None else (prog,)
        with state.lock:
            for p in progs:
                ui = self.prog_ui[p]
                state.progs[p].chord_map = [
                    parse_chord(c) for c in ui["chord_map"]
                ]
                state.progs[p].chord_delay = [
                    bool(v.get()) for v in ui["chord_delay"]
                ]
                xps = []
                for v in ui["chord_xpose"]:
                    try:
                        xps.append(clamp(int(v.get()), TRANSPOSE_MIN, TRANSPOSE_MAX))
                    except (tk.TclError, ValueError):
                        xps.append(0)
                state.progs[p].chord_xpose = xps
                chs, gl = [], []
                for v in ui["chord_ch"]:
                    try:
                        chs.append(clamp(int(v.get()), 1, 16))
                    except (tk.TclError, ValueError):
                        chs.append(1)
                for v in ui["chord_ch_global"]:
                    gl.append(bool(v.get()))
                state.progs[p].chord_ch = chs
                state.progs[p].chord_ch_global = gl
        self._apply_local_spin_states()

    def _on_chord_learned(self, prog, slot, notes):
        self.root.after(0, self._apply_chord_learned, prog, slot, notes)

    def _apply_chord_learned(self, prog, slot, notes):
        try:
            self._set_chord(prog, slot, notes)
        except tk.TclError:
            pass

    def _on_clip_learned(self, prog, slot, notes):
        self.root.after(0, self._apply_clip_learned, prog, slot, notes)

    def _apply_clip_learned(self, prog, slot, notes):
        try:
            self._set_clip(prog, slot, notes)
        except tk.TclError:
            pass

    def _sync_clip_overdub(self, prog):
        ui = self.prog_ui[prog]
        with state.lock:
            state.clip_overdub[prog] = bool(ui["clip_overdub"].get())

    def _set_clip(self, prog, slot, notes):
        notes = parse_clip(notes)
        ui = self.prog_ui[prog]
        ui["clip_map"][slot] = notes
        self._refresh_clip_label(prog, slot)
        with state.lock:
            state.progs[prog].clip_map[slot] = [dict(e) for e in notes]

    def _refresh_clip_label(self, prog, slot):
        ui = self.prog_ui[prog]
        try:
            xp = int(ui["clip_xpose"][slot].get())
        except (tk.TclError, ValueError, KeyError):
            xp = 0
        if slot < len(ui["clip_labels"]):
            ui["clip_labels"][slot].set(format_clip(ui["clip_map"][slot], xpose=xp))

    def _on_clip_xpose(self, prog, slot):
        if self._syncing:
            return
        try:
            xp = clamp(int(self.prog_ui[prog]["clip_xpose"][slot].get()),
                       TRANSPOSE_MIN, TRANSPOSE_MAX)
        except (tk.TclError, ValueError):
            return
        with state.lock:
            state.progs[prog].clip_xpose[slot] = xp
        self._refresh_clip_label(prog, slot)

    def _sync_clips(self, prog=None):
        progs = range(4) if prog is None else (prog,)
        with state.lock:
            for p in progs:
                ui = self.prog_ui[p]
                state.progs[p].clip_map = [parse_clip(c) for c in ui["clip_map"]]
                state.progs[p].clip_delay = [bool(v.get()) for v in ui["clip_delay"]]
                xps, modes = [], []
                for v in ui["clip_xpose"]:
                    try:
                        xps.append(clamp(int(v.get()), TRANSPOSE_MIN, TRANSPOSE_MAX))
                    except (tk.TclError, ValueError):
                        xps.append(0)
                for v in ui["clip_mode"]:
                    modes.append("one-shot" if str(v.get()).lower().startswith("one")
                                 else "continuous")
                state.progs[p].clip_xpose = xps
                state.progs[p].clip_mode = modes
            state.clip_overdub = [
                bool(self.prog_ui[p]["clip_overdub"].get()) for p in range(len(self.prog_ui))
            ]

    def _clip_meta(self, prog, slot):
        ui = self.prog_ui[prog]
        try:
            xp = int(ui["clip_xpose"][slot].get())
        except (tk.TclError, ValueError):
            xp = 0
        return {
            "notes": parse_clip(ui["clip_map"][slot]),
            "delay": bool(ui["clip_delay"][slot].get()),
            "xpose": xp,
            "mode": ui["clip_mode"][slot].get(),
        }

    def _apply_clip_meta(self, prog, slot, meta):
        ui = self.prog_ui[prog]
        self._set_clip(prog, slot, meta["notes"])
        ui["clip_delay"][slot].set(bool(meta["delay"]))
        was = self._syncing
        self._syncing = True
        try:
            ui["clip_xpose"][slot].set(int(meta["xpose"]))
            ui["clip_mode"][slot].set(meta.get("mode") or "Continuous")
        finally:
            self._syncing = was
        self._refresh_clip_label(prog, slot)

    def _clip_press(self, prog, slot, event):
        try:
            orig = event.widget.cget("bg")
        except tk.TclError:
            orig = None
        self._clip_drag = (prog, slot, event.widget, orig, self._is_copy_mod(event))
        self._name_field_hl(event.widget, copy=self._clip_drag[4])

    def _clip_release(self, event):
        src = self._clip_drag
        dest = None
        try:
            w = event.widget.winfo_containing(event.x_root, event.y_root)
            while w is not None:
                dest = getattr(w, "_clip_ref", None)
                if dest:
                    break
                w = getattr(w, "master", None)
        except tk.TclError:
            dest = None
        if src:
            self._name_field_restore(src[2], src[3])
        self._clip_drag = None
        if not src or not dest:
            return
        sp, ss = src[0], src[1]
        dp, ds = dest
        if sp != dp:
            return
        if src[4]:
            self._apply_clip_meta(sp, ds, self._clip_meta(sp, ss))
            self._sync_clips(sp)
            self._append_log(f"PROG{sp + 1} copied clip Pad {ss + 1} → Pad {ds + 1}")
        else:
            ma, mb = self._clip_meta(sp, ss), self._clip_meta(sp, ds)
            self._apply_clip_meta(sp, ss, mb)
            self._apply_clip_meta(sp, ds, ma)
            self._sync_clips(sp)
            self._append_log(f"PROG{sp + 1} swapped clip Pad {ss + 1} ↔ Pad {ds + 1}")

    def _save_clip_patch(self, prog):
        self._sync_clips(prog)
        ui = self.prog_ui[prog]
        path = filedialog.asksaveasfilename(
            parent=self.root, title=f"Save PROG {prog + 1} clip patch",
            defaultextension=".txt",
            filetypes=[("Clip patch", "*.txt"), ("All files", "*.*")],
            initialfile=f"PROG{prog + 1}-clips.txt",
        )
        if not path:
            return
        lines = ["MiniMapper clip patch v1", f"name: PROG {prog + 1}"]
        for i in range(16):
            events = parse_clip(ui["clip_map"][i])
            if not events:
                continue
            try:
                xp = int(ui["clip_xpose"][i].get())
            except (tk.TclError, ValueError):
                xp = 0
            roll = "on" if ui["clip_delay"][i].get() else "off"
            mode = "one-shot" if str(ui["clip_mode"][i].get()).lower().startswith("one") else "continuous"
            lines.append(f"slot: {i} delay: {roll} xpose: {xp} mode: {mode}")
            for ev in events:
                ms = int(round(ev["delay"] * 1000.0))
                dur = int(round(ev["duration"] * 1000.0))
                lines.append(
                    f"  {ev['note']} {ms} {ev['vel']} {ev['ch']} {dur}"
                )
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
        except Exception as e:
            messagebox.showerror("Save patch", str(e))
            return
        self._append_log(f"PROG{prog + 1} clip patch saved → {path}")

    def _load_clip_patch(self, prog):
        path = filedialog.askopenfilename(
            parent=self.root, title=f"Load PROG {prog + 1} clip patch",
            filetypes=[("Clip patch", "*.txt"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as f:
                text = f.read()
        except Exception as e:
            messagebox.showerror("Load patch", str(e))
            return
        slots = [[] for _ in range(16)]
        delays = [True] * 16
        xposes = [0] * 16
        modes = ["Continuous"] * 16
        cur = None
        for raw in text.splitlines():
            line = raw.strip()
            if line.startswith("slot:"):
                parts = line.split()
                try:
                    cur = int(parts[1])
                except (ValueError, IndexError):
                    cur = None
                    continue
                if "delay:" in parts:
                    delays[cur] = parts[parts.index("delay:") + 1] != "off"
                if "xpose:" in parts:
                    try:
                        xposes[cur] = int(parts[parts.index("xpose:") + 1])
                    except (ValueError, IndexError):
                        pass
                if "mode:" in parts:
                    m = parts[parts.index("mode:") + 1]
                    modes[cur] = "One-shot" if m.startswith("one") else "Continuous"
                slots[cur] = []
            elif cur is not None and line and line[0].isdigit():
                bits = line.split()
                try:
                    n = int(bits[0])
                    ms = int(bits[1]) if len(bits) > 1 else 0
                    vel = int(bits[2]) if len(bits) > 2 else 100
                    ch = int(bits[3]) if len(bits) > 3 else 1
                    dur = int(bits[4]) if len(bits) > 4 else 250
                    slots[cur].append({
                        "note": n, "delay": ms / 1000.0, "vel": vel,
                        "ch": ch, "duration": dur / 1000.0,
                    })
                except ValueError:
                    pass
        ui = self.prog_ui[prog]
        for i in range(16):
            self._set_clip(prog, i, slots[i])
            try:
                ui["clip_delay"][i].set(bool(delays[i]))
                ui["clip_xpose"][i].set(int(xposes[i]))
                ui["clip_mode"][i].set(modes[i])
            except tk.TclError:
                pass
            self._refresh_clip_label(prog, i)
        self._sync_clips(prog)
        filled = sum(1 for s in slots if parse_clip(s))
        self._append_log(
            f"PROG{prog + 1} loaded clip patch ({filled} clips) from {os.path.basename(path)}"
        )

    def _is_copy_mod(self, event):
        # Alt / Option (Mac Option is 0x10 or 0x8 depending on Tk)
        return bool(event.state & (0x0008 | 0x0010 | 0x20000))

    def _name_field_hl(self, widget, copy=False):
        if widget is None:
            return
        bg = "#d8ead2" if copy else "#cde8ff"
        try:
            widget.configure(bg=bg)
            if widget.winfo_class() == "Label":
                widget.configure(fg="#111111")
        except tk.TclError:
            pass

    def _name_field_restore(self, widget, orig_bg=None):
        if widget is None:
            return
        bg = orig_bg or getattr(widget, "_name_bg", ChordNameSpin.NAME_BG)
        fg = getattr(widget, "_name_fg", ChordNameSpin.NAME_FG)
        try:
            widget.configure(bg=bg)
            if widget.winfo_class() == "Label":
                widget.configure(fg=fg)
        except tk.TclError:
            pass

    def _chord_press(self, prog, slot, event):
        try:
            orig = event.widget.cget("bg")
        except tk.TclError:
            orig = None
        self._chord_drag = (prog, slot, event.widget, orig, self._is_copy_mod(event))
        self._name_field_hl(event.widget, copy=self._chord_drag[4])

    def _chord_clear_drag_hl(self):
        drag = self._chord_drag
        if not drag:
            return
        self._name_field_restore(drag[2], drag[3])

    def _chord_release(self, event):
        src = self._chord_drag
        dest = None
        try:
            w = event.widget.winfo_containing(event.x_root, event.y_root)
            while w is not None:
                dest = getattr(w, "_chord_ref", None)
                if dest:
                    break
                w = getattr(w, "master", None)
        except tk.TclError:
            dest = None
        self._chord_clear_drag_hl()
        self._chord_drag = None
        if not src or not dest:
            return
        if src[0] != dest[0] or src[1] == dest[1]:
            return
        if src[4]:
            self._copy_chord(src[0], src[1], dest[1])
        else:
            self._swap_chords(src[0], src[1], dest[1])

    def _chord_meta(self, prog, slot):
        ui = self.prog_ui[prog]
        try:
            xp = int(ui["chord_xpose"][slot].get())
        except (tk.TclError, ValueError):
            xp = 0
        try:
            ch = clamp(int(ui["chord_ch"][slot].get()), 1, 16)
        except (tk.TclError, ValueError):
            ch = 1
        return {
            "notes": parse_chord(ui["chord_map"][slot]),
            "delay": bool(ui["chord_delay"][slot].get()),
            "xpose": xp,
            "ch": ch,
            "gl": bool(ui["chord_ch_global"][slot].get()),
        }

    def _apply_chord_meta(self, prog, slot, meta):
        ui = self.prog_ui[prog]
        self._set_chord(prog, slot, meta["notes"])
        ui["chord_delay"][slot].set(bool(meta["delay"]))
        was = self._syncing
        self._syncing = True
        try:
            ui["chord_xpose"][slot].set(int(meta["xpose"]))
            ui["chord_ch"][slot].set(int(meta["ch"]))
            ui["chord_ch_global"][slot].set(bool(meta["gl"]))
        finally:
            self._syncing = was
        self._refresh_chord_label(prog, slot)

    def _swap_chords(self, prog, a, b):
        a, b = int(a), int(b)
        if a == b or not (0 <= a <= 15 and 0 <= b <= 15):
            return
        self._sync_chords(prog)
        ma, mb = self._chord_meta(prog, a), self._chord_meta(prog, b)
        self._apply_chord_meta(prog, a, mb)
        self._apply_chord_meta(prog, b, ma)
        self._sync_chords(prog)
        self._append_log(f"PROG{prog + 1} swapped Pad {a + 1} ↔ Pad {b + 1}")

    def _copy_chord(self, prog, src, dst):
        src, dst = int(src), int(dst)
        if src == dst or not (0 <= src <= 15 and 0 <= dst <= 15):
            return
        self._sync_chords(prog)
        self._apply_chord_meta(prog, dst, self._chord_meta(prog, src))
        self._sync_chords(prog)
        self._append_log(f"PROG{prog + 1} copied Pad {src + 1} → Pad {dst + 1}")

    def _kb_press(self, slot, event):
        try:
            orig = event.widget.cget("bg")
        except tk.TclError:
            orig = None
        self._kb_drag = (int(slot), event.widget, orig, self._is_copy_mod(event))
        try:
            event.widget.configure(bg="#d8ead2" if self._kb_drag[3] else "#cde8ff")
        except tk.TclError:
            pass

    def _kb_release(self, event):
        src = self._kb_drag
        dest = None
        try:
            w = event.widget.winfo_containing(event.x_root, event.y_root)
            while w is not None:
                dest = getattr(w, "_kb_ref", None)
                if dest is not None:
                    break
                w = getattr(w, "master", None)
        except tk.TclError:
            dest = None
        if src:
            try:
                if src[2]:
                    src[1].configure(bg=src[2])
            except tk.TclError:
                pass
        self._kb_drag = None
        if src is None or dest is None:
            return
        a, copy = src[0], src[3]
        b = int(dest)
        if a == b:
            return
        self._move_knob_bank(a, b, copy=copy)

    def _move_knob_bank(self, a, b, copy=False):
        a, b = int(a), int(b)
        if not (0 <= a <= 15 and 0 <= b <= 15) or a == b:
            return
        self._sync_knob_names()
        self._sync_knob_ccs()
        with state.lock:
            names = list(state.knob_bank_names)
            ccs = [list(row) for row in state.knob_ccs]
            gl = list(state.knob_ch_global)
            chs = normalize_knob_ch(state.knob_ch)
            if copy:
                names[b] = names[a]
                ccs[b] = list(ccs[a])
                gl[b] = gl[a]
                chs[b] = list(chs[a])
            else:
                names[a], names[b] = names[b], names[a]
                ccs[a], ccs[b] = ccs[b], ccs[a]
                gl[a], gl[b] = gl[b], gl[a]
                chs[a], chs[b] = chs[b], chs[a]
            state.knob_bank_names = names
            state.knob_ccs = ccs
            state.knob_ch_global = gl
            state.knob_ch = chs
        was = self._syncing
        self._syncing = True
        try:
            for i in range(16):
                self.kb_name_vars[i].set(names[i])
                self.kb_ch_global[i].set(bool(gl[i]))
        finally:
            self._syncing = was
        self._load_knob_editor(self._kb_shown)
        verb = "copied" if copy else "swapped"
        self._append_log(f"Knob bank {verb} {a + 1} {'→' if copy else '↔'} {b + 1}")

    def _save_chord_patch(self, prog):
        self._sync_chords(prog)
        ui = self.prog_ui[prog]
        path = filedialog.asksaveasfilename(
            parent=self.root,
            title=f"Save PROG {prog + 1} chord patch",
            defaultextension=".txt",
            filetypes=[("Chord patch", "*.txt"), ("All files", "*.*")],
            initialfile=f"PROG{prog + 1}-chords.txt",
        )
        if not path:
            return
        delays = [bool(v.get()) for v in ui["chord_delay"]]
        xposes, chs, globs = [], [], []
        for i in range(16):
            try:
                xposes.append(int(ui["chord_xpose"][i].get()))
            except (tk.TclError, ValueError):
                xposes.append(0)
            try:
                chs.append(int(ui["chord_ch"][i].get()))
            except (tk.TclError, ValueError):
                chs.append(1)
            globs.append(bool(ui["chord_ch_global"][i].get()))
        text = serialize_chord_patch(
            f"PROG {prog + 1}", ui["chord_map"], delays, xposes, chs, globs,
        )
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
        except Exception as e:
            messagebox.showerror("Save patch", str(e))
            return
        self._append_log(f"PROG{prog + 1} chord patch saved → {path}")

    def _load_chord_patch(self, prog):
        path = filedialog.askopenfilename(
            parent=self.root,
            title=f"Load PROG {prog + 1} chord patch",
            filetypes=[("Chord patch", "*.txt"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as f:
                text = f.read()
            name, slots, delays, xposes, chs, globs, _ccs, _srcs = parse_chord_patch(text)
        except Exception as e:
            messagebox.showerror("Load patch", str(e))
            return
        ui = self.prog_ui[prog]
        for i in range(16):
            self._set_chord(prog, i, slots[i])
            try:
                ui["chord_delay"][i].set(bool(delays[i]))
                ui["chord_xpose"][i].set(int(xposes[i]))
                ui["chord_ch"][i].set(int(chs[i]))
                ui["chord_ch_global"][i].set(bool(globs[i]))
            except tk.TclError:
                pass
            self._refresh_chord_label(prog, i)
        self._sync_chords(prog)
        filled = sum(1 for s in slots if parse_chord(s))
        self._append_log(
            f"PROG{prog + 1} loaded patch '{name}' ({filled} chords) from {os.path.basename(path)}"
        )

    def _export_chord_midi(self, prog):
        self._sync_chords(prog)
        ui = self.prog_ui[prog]
        filled = [
            i for i in range(16) if parse_chord(ui["chord_map"][i])
        ]
        if not filled:
            messagebox.showinfo("Export MIDI", "No learned chords to export.")
            return
        mode = {"v": None}

        def pick(v):
            mode["v"] = v
            win.destroy()

        win = tk.Toplevel(self.root)
        win.title("Export MIDI")
        win.transient(self.root)
        win.resizable(False, False)
        tk.Label(
            win,
            text="Export filled chords as:",
            justify="left",
        ).pack(padx=16, pady=(14, 8))
        tk.Button(
            win, text="One file per chord", width=28,
            command=lambda: pick("each"),
        ).pack(padx=16, pady=4)
        tk.Button(
            win, text="One file — consecutive, ½ bar each", width=28,
            command=lambda: pick("seq"),
        ).pack(padx=16, pady=4)
        tk.Button(win, text="Cancel", width=12, command=win.destroy).pack(pady=(8, 14))
        win.protocol("WM_DELETE_WINDOW", win.destroy)
        win.grab_set()
        win.wait_window()
        if mode["v"] is None:
            return
        if mode["v"] == "seq":
            self._export_chord_midi_sequence(prog, filled)
        else:
            self._export_chord_midi_each(prog, filled)

    def _export_chord_midi_each(self, prog, filled):
        ui = self.prog_ui[prog]
        folder = filedialog.askdirectory(
            parent=self.root,
            title=f"Folder for PROG {prog + 1} chord MIDI files",
        )
        if not folder:
            return
        dest = os.path.join(folder, f"PROG{prog + 1}-chords")
        try:
            os.makedirs(dest, exist_ok=True)
        except Exception as e:
            messagebox.showerror("Export MIDI", str(e))
            return
        n = 0
        for i in filled:
            events = parse_chord(ui["chord_map"][i])
            try:
                xp = int(ui["chord_xpose"][i].get())
            except (tk.TclError, ValueError):
                xp = 0
            events = [
                {"note": clamp_note(ev["note"] + xp), "delay": ev["delay"], "vel": ev["vel"]}
                for ev in events
            ]
            use_delay = bool(ui["chord_delay"][i].get())
            names = "-".join(format_note(ev["note"]) for ev in events) or "chord"
            fname = f"PC{i:02d}_{names}.mid"
            fname = "".join(c if c.isalnum() or c in "._-" else "_" for c in fname)
            path = os.path.join(dest, fname)
            try:
                if write_chord_midi(path, events, use_delay=use_delay,
                                    name=f"PC{i:02d} {format_chord(events)}"):
                    n += 1
            except Exception as e:
                self._append_log(f"MIDI export PC{i:02d} failed: {e}")
        self._append_log(f"PROG{prog + 1} exported {n} MIDI file(s) → {dest}")
        messagebox.showinfo("Export MIDI", f"Wrote {n} file(s) to:\n{dest}")

    def _export_chord_midi_sequence(self, prog, filled):
        ui = self.prog_ui[prog]
        path = filedialog.asksaveasfilename(
            parent=self.root,
            title=f"Save PROG {prog + 1} chords as one MIDI file",
            defaultextension=".mid",
            filetypes=[("MIDI", "*.mid"), ("All files", "*.*")],
            initialfile=f"PROG{prog + 1}-chords.mid",
        )
        if not path:
            return
        chords = []
        for i in filled:
            try:
                xp = int(ui["chord_xpose"][i].get())
            except (tk.TclError, ValueError):
                xp = 0
            chords.append((
                ui["chord_map"][i],
                bool(ui["chord_delay"][i].get()),
                xp,
            ))
        try:
            ok = write_chord_midi_sequence(
                path, chords, name=f"PROG{prog + 1} chords",
            )
        except Exception as e:
            messagebox.showerror("Export MIDI", str(e))
            return
        if not ok:
            messagebox.showinfo("Export MIDI", "No learned chords to export.")
            return
        self._append_log(f"PROG{prog + 1} exported {len(filled)} chords (½ bar each) → {path}")
        messagebox.showinfo("Export MIDI", f"Wrote {len(filled)} chord(s) to:\n{path}")

    def start_filter(self):
        try:
            self._sync_all_progs()
            if self.filter:
                self.filter.stop()
                self.filter = None

            mpk_in = pick_mpk_port(list_midi_inputs())
            mpk_out = pick_mpk_port(list_midi_outputs())
            if not mpk_in or not mpk_out:
                messagebox.showerror("Error", "MPK Mini not found.")
                return

            virt_choice = (self.virt_out_var.get() or "").strip()
            daw_choice = (self.daw_out_var.get() or "").strip()
            virtual_port = None
            if virt_choice == VIRT_CREATE:
                try:
                    virtual_port = mido.open_output("Minimapper", virtual=True)
                except Exception as e:
                    if IS_WIN:
                        messagebox.showerror(
                            "To DAW",
                            "Windows cannot create a virtual MIDI port.\n\n"
                            "Install loopMIDI, create a port named Minimapper,\n"
                            "click Ports, and pick it in To DAW.",
                        )
                        return
                    raise RuntimeError(f"Could not create virtual port: {e}") from e
            elif virt_choice and virt_choice not in ("None",):
                virtual_port = mido.open_output(virt_choice)
            elif IS_WIN:
                messagebox.showerror(
                    "To DAW",
                    "Pick a loopMIDI (or similar) port in To DAW.\n"
                    "Windows cannot create a virtual MIDI port.",
                )
                return

            daw_out_port = None
            if daw_choice not in ("", "None") and daw_choice != virt_choice:
                daw_out_port = mido.open_output(daw_choice)

            self.filter = MidiFilter(
                mpk_in,
                mpk_out,
                daw_out_port,
                virtual_port=virtual_port,
                on_state_change=self._on_state_change,
                on_log=self._append_log,
                on_init_status=self._on_init_status,
                on_chord_learned=self._on_chord_learned,
                on_clip_learned=self._on_clip_learned,
            )
            self.filter.start()
            self.start_btn.config(state="disabled")
            self.stop_btn.config(state="normal")
            self.panic_btn.config(state="normal")
            self._set_sync_dots("pending")
            dest = virt_choice if virt_choice != VIRT_CREATE else "Minimapper (virtual)"
            self._append_log(f"MIDI filter running → {dest}")
            self.root.after(150, self._auto_initialize)
            self._append_log(self._hid_hint(self.hid.available()))
        except Exception as e:
            messagebox.showerror("Error", f"Unable to start filter:\n{e}")

    def stop_filter(self):
        if self.filter:
            self.filter.stop()
            self.filter = None
        self._set_dpad(None)
        self.start_btn.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.panic_btn.config(state="disabled")
        self._set_sync_dots("fail")

    def panic(self):
        if self.filter:
            self.filter.panic()
            self._append_log("Panic: all held notes off.")
        self._set_dpad(None)

    def _auto_initialize(self):
        if self.filter:
            self.filter.initialize_mpk()

    def _on_init_status(self, prog, status):
        self.root.after(0, self._apply_init_status, prog, status)

    def _apply_init_status(self, prog, status):
        try:
            if prog is None:
                self._set_sync_dots(status)
                return
            if 0 <= int(prog) < 4:
                self._paint_dot(self._sync_dots[int(prog)], status)
        except tk.TclError:
            pass

    def _set_sync_dots(self, status):
        for dot in self._sync_dots:
            self._paint_dot(dot, status)

    def _paint_dot(self, dot, status):
        if status == "ok":
            color = "#2ecc40"
        else:
            color = "#cc3333"
        try:
            dot.config(fg=color)
        except tk.TclError:
            pass

    def on_close(self):
        try:
            if self.filter:
                self.filter.stop()
            self._set_dpad(None)
        finally:
            self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    try:
        MidiGUI(root)
    except Exception as exc:
        try:
            messagebox.showerror("MiniMapper", f"Startup failed:\n{exc}")
        except Exception:
            print(f"Startup failed: {exc}")
        raise
    root.mainloop()
