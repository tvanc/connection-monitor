#!/usr/bin/env python3
"""Monitors internet connectivity, logs state changes, and reports uptime and drops.

  python3 main.py              # monitor with a live dashboard (Ctrl+C to stop)
  python3 main.py --report     # show stats from the log
  python3 main.py --report --since 24h      # last 24 hours (also 7d, or 2026-10-17 08:00)
  python3 main.py --compact    # convert an older per-check log to the compact format
  python3 main.py --upgrade    # add the Network column to an older log (done automatically on start)
  python3 main.py --quiet      # no dashboard, only print up/down events

The router (default gateway, auto-detected or set with --router-ip) is pinged
separately. If the internet is down but the router answers, the fault is
upstream of your network (modem/ISP); if the router is down too, it's local
(router, cabling or Wi-Fi on this computer).

A check is "down" only when ALL targets fail to answer a ping, so one flaky
server doesn't count as an outage.

The log only gets a row when something changes (internet, router, connection
type or Wi-Fi network), plus a "still alive" row every --heartbeat seconds, so a row's state holds
until the next row. A STOP row is written on exit; time between a STOP (or a
crash/power loss, seen as a missing heartbeat) and the next start is reported
as "not monitored" instead of counting as up or down. If you change --heartbeat,
pass the same value to --report.

Self-update: when run from a plain copy of the files (not a git checkout), it checks GitHub on start-up and,
if there's a newer commit, replaces main.py (and start.command / start.bat if present) and restarts. A git
checkout (a .git folder next to the script) is never touched, so local development isn't disturbed. Skip the
check with --no-update or by setting CONNECTION_MONITOR_NO_UPDATE=1.

Works on macOS (primary target), Linux and Windows. Standard library only, except that the full-screen
dashboard and the pretty report use the 'rich' package when it's installed (pip3 install rich); without
it, or with --plain, everything falls back to simple text output.

Dashboard: click a tab (a connection such as router-ethernet or router-wifi [Home]) and both the stats
and the drops list follow it. Click a red/yellow square in the timelines to jump to that drop. Mouse
wheel / arrow keys / PgUp / PgDn scroll the list, End follows the newest, ? shows/hides the legend,
q (or Ctrl+C) stops.
"""
import argparse
import csv
import ipaddress
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import urllib.request
from datetime import datetime, timedelta
from pathlib import Path
from types import SimpleNamespace
import _thread
import threading

try:
    from rich import box
    from rich.cells import cell_len
    from rich.console import Console, Group
    from rich.live import Live
    from rich.panel import Panel
    from rich.rule import Rule
    from rich.table import Table
    from rich.text import Text
    HAVE_RICH = True
except ImportError:
    HAVE_RICH = False

SYSTEM = platform.system()  # 'Darwin', 'Linux', 'Windows'
TS_FORMAT = '%Y-%m-%d %H:%M:%S'
COLUMNS = ['Timestamp', 'Status', 'LatencyMs', 'Router', 'ConnType', 'Network']
HEADER = ','.join(COLUMNS)
SQUARE = '■'
COLORS = {'red': '31', 'green': '32', 'yellow': '33', 'cyan': '36'}

ACCENT = '#a78bfa'   # violet
OK = '#4ade80'       # green
WARN = '#fbbf24'     # amber
BAD = '#f87171'      # red
DIM = 'grey50'


def enable_windows_vt():
    """Turn on ANSI/VT processing for the Windows console so Rich can use the alternate screen."""
    if os.name != 'nt':
        return False
    try:
        import ctypes
        k32 = ctypes.windll.kernel32
        handle = k32.GetStdHandle(-11)  # STD_OUTPUT_HANDLE
        mode = ctypes.c_uint32()
        if not k32.GetConsoleMode(handle, ctypes.byref(mode)):
            return False  # not a real console (redirected)
        return bool(k32.SetConsoleMode(handle, mode.value | 0x0004))  # ENABLE_VIRTUAL_TERMINAL_PROCESSING
    except Exception:
        return False


console = Console(highlight=False, legacy_windows=False if enable_windows_vt() else None) if HAVE_RICH else None


# ---------------------------------------------------------------- helpers

def run(cmd, timeout=5):
    """Run a command, returning its stdout ('' on any failure)."""
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).stdout
    except Exception:
        return ''


def format_span(seconds):
    seconds = max(0, seconds)
    if seconds < 60:
        return f'{seconds:.0f}s'
    if seconds < 3600:
        return f'{int(seconds // 60)}m {int(seconds % 60):02d}s'
    return f'{int(seconds // 3600)}h {int(seconds % 3600 // 60):02d}m'


def color(text, name):
    if not name or not sys.stdout.isatty():
        return text
    return f'\033[{COLORS[name]}m{text}\033[0m'


def parse_since(text):
    """'24h', '7d', '90m', or an ISO date/time."""
    if not text:
        return datetime.min
    m = re.fullmatch(r'(\d+)([mhd])', text.strip().lower())
    if m:
        unit = {'m': 'minutes', 'h': 'hours', 'd': 'days'}[m.group(2)]
        return datetime.now() - timedelta(**{unit: int(m.group(1))})
    return datetime.fromisoformat(text)


# ---------------------------------------------------------------- network probes

def ping(host, timeout_ms):
    """Round-trip time in ms if the host answered, else None. Uses the system ping (no root needed)."""
    if SYSTEM == 'Windows':
        cmd = ['ping', '-n', '1', '-w', str(timeout_ms), host]
    elif SYSTEM == 'Darwin':
        cmd = ['ping', '-c', '1', '-W', str(timeout_ms), host]  # macOS -W is milliseconds
    else:
        cmd = ['ping', '-c', '1', '-W', str(max(1, -(-timeout_ms // 1000))), host]  # Linux -W is seconds
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_ms / 1000 + 3)
    except Exception:
        return None
    if p.returncode != 0:
        return None
    if SYSTEM == 'Windows' and 'TTL=' not in p.stdout:  # Windows exits 0 on "host unreachable" replies
        return None
    m = re.search(r'time[=<]\s*([\d.]+)', p.stdout)
    return round(float(m.group(1))) if m else 0


def parse_route_darwin(text):
    gw = re.search(r'gateway:\s*(\S+)', text)
    ifc = re.search(r'interface:\s*(\S+)', text)
    return (gw.group(1) if gw else None, ifc.group(1) if ifc else None)


def parse_route_linux(text):
    m = re.search(r'default via (\S+)(?: dev (\S+))?', text)
    return (m.group(1), m.group(2)) if m else (None, None)


# Windows keeps default routes for adapters that are unplugged or disconnected, so `route print` can name an
# adapter that isn't actually in use. Ask PowerShell for the best default route over an adapter that is Up.
_WIN_ROUTE_SCRIPT = (
    "$r = Get-NetRoute -DestinationPrefix '0.0.0.0/0' -ErrorAction SilentlyContinue | ForEach-Object { "
    "$a = Get-NetAdapter -InterfaceIndex $_.ifIndex -ErrorAction SilentlyContinue; "
    "if ($a -and $a.Status -eq 'Up') { [pscustomobject]@{ Hop = $_.NextHop; Idx = $a.ifIndex; "
    "Media = $a.PhysicalMediaType; Metric = $_.RouteMetric + $_.InterfaceMetric } } } "
    "| Sort-Object Metric | Select-Object -First 1; "
    "if ($r) { $ip = (Get-NetIPAddress -InterfaceIndex $r.Idx -AddressFamily IPv4 -ErrorAction SilentlyContinue "
    "| Select-Object -First 1).IPAddress; "
    "$p = (Get-NetConnectionProfile -InterfaceIndex $r.Idx -ErrorAction SilentlyContinue | Select-Object -First 1).Name; "
    "'{0}|{1}|{2}|{3}' -f $r.Hop, $ip, $r.Media, $p }"
)


def windows_active_route():
    """(gateway, local ip, 'wifi'/'ethernet'/'other', network profile name) of the default route in use, or
    None if there isn't one. For Wi-Fi the profile name is normally the network's name (SSID)."""
    out = run(['powershell', '-NoProfile', '-NonInteractive', '-Command', _WIN_ROUTE_SCRIPT], timeout=20).strip()
    parts = out.splitlines()[-1].split('|') if out else []
    if len(parts) != 4 or not parts[0]:
        return None
    gateway, ip, media, profile = parts
    return (gateway, ip or None, 'wifi' if '802.11' in media else 'ethernet' if '802.3' in media else 'other',
            profile or None)


def default_route():
    """(gateway ip, interface name) of the default route, or (None, None). On Windows the second item is
    the local IP address instead of a name."""
    if SYSTEM == 'Darwin':
        return parse_route_darwin(run(['route', '-n', 'get', 'default']))
    if SYSTEM == 'Linux':
        return parse_route_linux(run(['ip', '-4', 'route', 'show', 'default']))
    info = windows_active_route()
    return (info[0], info[1]) if info else (None, None)


def parse_hardware_ports(text):
    """networksetup -listallhardwareports -> {device: port name}."""
    ports, port = {}, None
    for line in text.splitlines():
        if line.startswith('Hardware Port:'):
            port = line.split(':', 1)[1].strip()
        elif line.startswith('Device:') and port:
            ports[line.split(':', 1)[1].strip()] = port
    return ports


def interface_ip(iface):
    if SYSTEM == 'Darwin':
        return run(['ipconfig', 'getifaddr', iface]).strip() or None
    if SYSTEM == 'Linux':
        m = re.search(r'inet (\d+\.\d+\.\d+\.\d+)', run(['ip', '-4', '-o', 'addr', 'show', 'dev', iface]))
        return m.group(1) if m else None
    return None


def interface_media(iface):
    if SYSTEM == 'Darwin':
        port = parse_hardware_ports(run(['networksetup', '-listallhardwareports'])).get(iface, '').lower()
        if 'wi-fi' in port or 'airport' in port:
            return 'wifi'
        if any(k in port for k in ('ethernet', 'lan', 'thunderbolt')):
            return 'ethernet'
        return 'other'
    if SYSTEM == 'Linux':
        return 'wifi' if Path(f'/sys/class/net/{iface}/wireless').exists() else 'ethernet'
    return 'other'


def clean_ssid(name):
    name = (name or '').strip()
    return None if not name or '<redacted>' in name.lower() else name


def parse_ssid_networksetup(text):
    m = re.match(r'Current Wi-Fi Network:\s*(.+)', text.strip())
    return clean_ssid(m.group(1)) if m else None


def parse_ssid_ipconfig(text):
    m = re.search(r'^\s*SSID\s*:\s*(.+?)\s*$', text, re.M)
    return clean_ssid(m.group(1)) if m else None


def parse_ssid_system_profiler(text):
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.strip().rstrip(':') == 'Current Network Information':
            for nxt in lines[i + 1:]:
                if nxt.strip():
                    return clean_ssid(nxt.strip().rstrip(':'))
    return None


def parse_ssid_nmcli(text):
    for line in text.splitlines():
        if line.startswith('yes:'):
            return clean_ssid(line[4:].replace('\\:', ':'))
    return None


def parse_ssid_netsh(text):
    m = re.search(r'^\s*SSID\s*:\s*(.+?)\s*$', text, re.M)  # BSSID lines don't match: they start with "BSSID"
    return clean_ssid(m.group(1)) if m else None


_profiler_cache = (-1e9, None)
_shortcut_cache = (-1e9, None)
SHORTCUT_NAME = 'Wi-Fi Name'  # macOS Shortcut that returns the Wi-Fi network name (see --wifi-shortcut)


def ssid_from_shortcut():
    """macOS hides the Wi-Fi name from scripts that lack Location Services permission, but the Shortcuts app
    has its own permission. A shortcut named SHORTCUT_NAME containing "Get Network Details" (Wi-Fi, Network
    Name) can therefore read it. Slow-ish, so the answer is remembered for a minute."""
    global _shortcut_cache
    if time.monotonic() - _shortcut_cache[0] < 60:
        return _shortcut_cache[1]
    ssid = None
    exe = shutil.which('shortcuts')
    if exe:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'ssid.txt'
            run([exe, 'run', SHORTCUT_NAME, '--output-path', str(out), '--output-type', 'public.plain-text'],
                timeout=20)
            try:
                ssid = clean_ssid(out.read_text(errors='ignore'))
            except OSError:
                pass
    _shortcut_cache = (time.monotonic(), ssid)
    return ssid


def wifi_ssid(iface):
    """Name of the Wi-Fi network we're on, or None if it can't be read."""
    global _profiler_cache
    if SYSTEM == 'Darwin':
        ssid = (parse_ssid_networksetup(run(['networksetup', '-getairportnetwork', iface]))
                or parse_ssid_ipconfig(run(['ipconfig', 'getsummary', iface])))
        ssid = ssid or ssid_from_shortcut()
        if ssid:
            return ssid
        # Slow last resort (a couple of seconds), so remember its answer for 5 minutes.
        if time.monotonic() - _profiler_cache[0] > 300:
            _profiler_cache = (time.monotonic(),
                               parse_ssid_system_profiler(run(['system_profiler', 'SPAirPortDataType'], timeout=20)))
        return _profiler_cache[1]
    if SYSTEM == 'Linux':
        out = run(['iwgetid', '-r']).strip()
        return clean_ssid(out) or parse_ssid_nmcli(run(['nmcli', '-t', '-f', 'active,ssid', 'dev', 'wifi']))
    return parse_ssid_netsh(run(['netsh', 'wlan', 'show', 'interfaces']))


def connection():
    """(connection type, Wi-Fi network name) of this computer.

    The type is e.g. router-ethernet, router-wifi, modem-ethernet. router vs modem is inferred: a
    private/CGNAT IP means we're behind a router (NAT); a public IP means plugged straight into a modem.
    The network is the Wi-Fi name ('unknown' if it can't be read) and blank when not on Wi-Fi.
    """
    try:
        if SYSTEM == 'Windows':
            info = windows_active_route()
            if not info:
                return 'no-link', ''
            gw, ip, media, profile = info
            iface = None
        else:
            gw, iface = default_route()
            if not gw or not iface:
                return 'no-link', ''
            ip, media = interface_ip(iface), interface_media(iface)
        via = 'router' if not ip or not ipaddress.ip_address(ip).is_global else 'modem'
        if media != 'wifi':
            return f'{via}-{media}', ''
        # Windows can hide the SSID from netsh (it needs Location access); the connection profile name is the fallback.
        return f'{via}-{media}', wifi_ssid(iface) or (profile if SYSTEM == 'Windows' else None) or 'unknown'
    except Exception:
        return 'unknown', ''


def label(conn, network):
    return f'{conn} [{network}]' if network else conn


def tab_key(conn, network):
    """The dashboard tab a connection belongs to: 'ethernet', the Wi-Fi network's name, or 'other' for everything
    else (no link, VPN, Wi-Fi whose network name couldn't be read...)."""
    if conn.endswith('-ethernet'):
        return 'ethernet'
    if conn.endswith('-wifi') and network and network != 'unknown':
        return network
    return 'other'


def tab_title(key):
    """How a tab is written on screen."""
    return 'Other' if key == 'other' else key


# ---------------------------------------------------------------- keep the computer awake

def keep_awake():
    """Prevent idle sleep while monitoring (the screen can still turn off). Returns a cleanup callable."""
    try:
        if SYSTEM == 'Darwin' and shutil.which('caffeinate'):
            p = subprocess.Popen(['caffeinate', '-i', '-w', str(os.getpid())])  # ends when we do
            return p.terminate
        if SYSTEM == 'Linux' and shutil.which('systemd-inhibit'):
            p = subprocess.Popen(['systemd-inhibit', '--what=idle:sleep', '--who=watch_internet',
                                  '--why=Monitoring internet connection', 'sleep', 'infinity'])
            return p.terminate
        if SYSTEM == 'Windows':
            import ctypes
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)  # ES_CONTINUOUS | ES_SYSTEM_REQUIRED
            return lambda: ctypes.windll.kernel32.SetThreadExecutionState(0x80000000)
    except Exception:
        pass
    return lambda: None


# ---------------------------------------------------------------- log reading / report

def load_rows(path, since):
    rows = []
    with open(path, newline='') as f:
        for r in csv.DictReader(f):
            try:
                t = datetime.strptime(r['Timestamp'], TS_FORMAT)
            except (ValueError, KeyError, TypeError):
                continue
            status = r.get('Status') or ''
            rows.append({'t': t, 'up': status == 'UP', 'stop': status == 'STOP', 'status': status,
                         'ms': r.get('LatencyMs') or '', 'router': r.get('Router') or '',
                         # rows logged before the ConnType column existed were router-ethernet
                         'conn': r.get('ConnType') or 'router-ethernet'})
            # rows logged before the Network column existed: Wi-Fi network unknown
            rows[-1]['network'] = r.get('Network') or ('unknown' if rows[-1]['conn'].endswith('wifi') else '')
            rows[-1]['label'] = label(rows[-1]['conn'], rows[-1]['network'])
            rows[-1]['tab'] = tab_key(rows[-1]['conn'], rows[-1]['network'])
    rows = [r for r in rows if r['t'] >= since]
    rows.sort(key=lambda r: r['t'])
    return rows


def analyze(args, since):
    """Reads the log and works out uptime, drops and per-connection stats.
    Returns (stats, None), or (None, message) when there's nothing to show yet."""
    if not Path(args.log_file).exists():
        return None, f'No log yet at {args.log_file}'
    rows = load_rows(args.log_file, since)
    max_gap = 2 * args.heartbeat + 30  # longer silence = monitoring wasn't running
    now = datetime.now()
    # If monitoring is still running, the last state holds up to now.
    if rows and not rows[-1]['stop'] and (now - rows[-1]['t']).total_seconds() <= max_gap:
        rows.append({**rows[-1], 't': now, 'ms': ''})
    if len(rows) < 2:
        return None, 'Not enough data yet.'

    up_s = down_s = unmonitored = 0.0
    outages, by_conn, by_tab = [], {}, {}
    start = start_label = start_net = start_tab = start_raw = None
    router_down = router_known = 0.0

    for i, r in enumerate(rows):
        nxt = rows[i + 1] if i + 1 < len(rows) else None
        dt = (nxt['t'] - r['t']).total_seconds() if nxt else 0
        weight = max(dt, 1)
        gap = False
        if r['stop']:
            if nxt:
                unmonitored += dt  # time after a STOP until monitoring resumed
        else:
            gap = dt > max_gap
            if gap:
                unmonitored += dt
                dt = 0
            c = by_conn.setdefault(r['label'], {'up': 0.0, 'down': 0.0})
            tb = by_tab.setdefault(r['tab'], {'up': 0.0, 'down': 0.0})
            if r['up']:
                up_s += dt
                c['up'] += dt
                tb['up'] += dt
            else:
                down_s += dt
                c['down'] += dt
                tb['down'] += dt
                if start is None:
                    start, start_label, start_net, start_tab, start_raw = r['t'], r['label'], r['network'], r['tab'], r['conn']
                    router_down, router_known = 0.0, 0.0
                if r['router']:
                    router_known += weight
                    if r['router'] == 'DOWN':
                        router_down += weight
        if start is not None and (r['stop'] or r['up'] or gap or nxt is None):
            cause = 'unknown' if not router_known else ('LOCAL' if router_down * 2 > router_known else 'UPSTREAM')
            outages.append({'start': start, 'end': r['t'], 'secs': (r['t'] - start).total_seconds(),
                            'conn': start_label, 'network': start_net, 'tab': start_tab, 'raw': start_raw,
                            'modem': start_raw.startswith('modem'), 'cause': cause,
                            'ongoing': not r['up'] and not r['stop'] and not gap and nxt is None})
            start = None

    monitored = up_s + down_s
    return SimpleNamespace(
        rows=rows, outages=outages, by_conn=by_conn, by_tab=by_tab, up_s=up_s, down_s=down_s, unmonitored=unmonitored,
        monitored=monitored, pct=100 * up_s / monitored if monitored > 0 else 0,
        span_days=max((rows[-1]['t'] - rows[0]['t']).total_seconds() / 86400 - unmonitored / 86400, 1 / 86400),
        lat=[float(r['ms']) for r in rows if r['up'] and r['ms'] != '']), None


def build_report(args, since, recent=15):
    """The plain-text report as a list of (text, color) lines."""
    a, msg = analyze(args, since)
    if a is None:
        return [(msg, None)]
    out = []
    add = lambda text='', col=None: out.append((text, col))
    rows, outages, by_conn = a.rows, a.outages, a.by_tab
    add()
    add('=== Internet connection report ===', 'cyan')
    add(f"Period:        {rows[0]['t']:%m/%d/%Y %I:%M %p}  ->  {rows[-1]['t']:%m/%d/%Y %I:%M %p}")
    add(f'Monitored:     {format_span(a.monitored)}   (not monitored: {format_span(a.unmonitored)})')
    add(f'Uptime:        {a.pct:.3f}%', 'green' if a.pct >= 99.9 else 'yellow' if a.pct >= 99 else 'red')
    add(f'Downtime:      {format_span(a.down_s)}')
    if a.lat:
        add(f'Latency:       avg {sum(a.lat) / len(a.lat):.0f} ms, max {max(a.lat):.0f} ms')
    width = max([17] + [len(tab_title(n)) + 2 for n in by_conn])
    for name in sorted(by_conn):
        t = by_conn[name]['up'] + by_conn[name]['down']
        n = sum(1 for o in outages if o['tab'] == name)
        p = 100 * by_conn[name]['up'] / t if t > 0 else 0
        add(f'{tab_title(name) + ":":<{width}}{p:6.2f}% up over {format_span(t)}, {n} drop{"" if n == 1 else "s"}')

    add()
    add(f'Drops:         {len(outages)}', 'red' if outages else 'green')
    if outages:
        secs = [o['secs'] for o in outages]
        add(f'Frequency:     {len(outages) / (a.span_days * 24):.2f} per hour, {len(outages) / a.span_days:.1f} per day')
        if len(outages) > 1:
            gaps = [(outages[i]['start'] - outages[i - 1]['end']).total_seconds() / 60 for i in range(1, len(outages))]
            add(f'Between drops: avg {sum(gaps) / len(gaps):.0f} min')
        add(f'Duration:      avg {format_span(sum(secs) / len(secs))}, longest {format_span(max(secs))}, '
            f'shortest {format_span(min(secs))}')
        upstream = sum(1 for o in outages if o['cause'] == 'UPSTREAM')
        local = sum(1 for o in outages if o['cause'] == 'LOCAL')
        if upstream + local:
            add()
            add(f'Cause:         {upstream} upstream (router OK, internet down), {local} local (router unreachable)', 'yellow')
        add()
        add('Most recent drops:')
        for o in outages[-recent:]:
            add(f"  {o['start']:%Y-%m-%d %H:%M:%S}  lasted {format_span(o['secs']):<8} [{o['cause']}] {where(o)}"
                f"{'  (ongoing)' if o['ongoing'] else ''}")
    add()
    return out


def print_lines(lines, limit=None):
    for text, col in lines[:limit]:
        print(color(text, col))


# ---------------------------------------------------------------- log maintenance

def append_row(path, fields):
    with open(path, 'a', newline='') as f:
        csv.writer(f, lineterminator='\n').writerow(fields)


def write_rows(path, rows):
    with open(path, 'w', newline='') as f:
        csv.writer(f, lineterminator='\n').writerows(rows)


def backup_file(path):
    backup = f"{path}.{datetime.now():%Y%m%d-%H%M%S}.bak"
    shutil.copy2(path, backup)
    return backup


def upgrade_log(path):
    """Add the Network column to an older log in place (keeps a .bak). Returns the backup path, or None if
    nothing needed changing. Existing Wi-Fi rows get the network 'unknown'; everything else is left alone."""
    path = Path(path)
    if not path.exists():
        return None
    with open(path, newline='') as f:
        rows = list(csv.reader(f))
    if not rows or rows[0] == COLUMNS:
        return None
    old = rows[0]
    out = [COLUMNS]
    for r in rows[1:]:
        if not r:
            continue
        d = dict(zip(old, r))
        conn = d.get('ConnType', '')
        out.append([d.get('Timestamp', ''), d.get('Status', ''), d.get('LatencyMs', ''), d.get('Router', ''), conn,
                    d.get('Network') or ('unknown' if conn.endswith('wifi') else '')])
    backup = backup_file(path)
    write_rows(path, out)
    return backup


def compact(args):
    path = Path(args.log_file)
    if not path.exists():
        print(f'No log at {path}')
        return
    rows = load_rows(path, datetime.min)
    out = [COLUMNS]
    ts = lambda t: f'{t:{TS_FORMAT}}'
    kept = prev = None
    for i, r in enumerate(rows):
        # Old logs treated >30s of silence as "monitoring wasn't running": mark it with a STOP row.
        if prev and not prev['stop'] and (r['t'] - prev['t']).total_seconds() > 30:
            out.append([ts(prev['t']), 'STOP', '', '', '', ''])
            kept = None
        keep = (r['stop'] or i == len(rows) - 1 or kept is None or r['status'] != kept['status']
                or r['router'] != kept['router'] or r['label'] != kept['label']
                or (r['t'] - kept['t']).total_seconds() >= args.heartbeat)
        if keep:
            out.append([ts(r['t']), 'STOP', '', '', '', ''] if r['stop']
                       else [ts(r['t']), r['status'], r['ms'], r['router'], r['conn'], r['network']])
            kept = r
        prev = r
    backup = backup_file(path)
    write_rows(path, out)
    print(f'Compacted {len(rows)} rows to {len(out) - 1}. Original saved as {backup}')


# ---------------------------------------------------------------- rich UI

CAUSE_COLOUR = {'UPSTREAM': WARN, 'LOCAL': BAD, 'unknown': DIM}


def scope_view(a, key):
    """The numbers for the whole log (key None) or for one tab/connection."""
    if key is None:
        return SimpleNamespace(name='All connections', pct=a.pct, down_s=a.down_s, outages=a.outages, lat=a.lat,
                               monitored=a.monitored, first=a.rows[0]['t'], last=a.rows[-1]['t'])
    c = a.by_tab.get(key, {'up': 0.0, 'down': 0.0})
    total = c['up'] + c['down']
    rows = [r for r in a.rows if r['tab'] == key and not r['stop']]
    return SimpleNamespace(
        name=tab_title(key), pct=100 * c['up'] / total if total > 0 else 0, down_s=c['down'],
        outages=[o for o in a.outages if o['tab'] == key], monitored=total,
        lat=[float(r['ms']) for r in rows if r['up'] and r['ms'] != ''],
        first=rows[0]['t'] if rows else a.rows[0]['t'], last=rows[-1]['t'] if rows else a.rows[-1]['t'])


def stat_cards(v):
    """Panel of big numbers over dim labels: uptime, downtime, drops, average drop, latency."""
    colour = OK if v.pct >= 99.9 else WARN if v.pct >= 99 else BAD
    n = len(v.outages)
    avg = sum(o['secs'] for o in v.outages) / n if n else None
    t = Table.grid(padding=(0, 2), expand=True)
    for _ in range(5):
        t.add_column(justify='center', ratio=1)
    t.add_row(
        Text.assemble((f'{v.pct:.3f}%' if v.monitored > 0 else '—', f'bold {colour}' if v.monitored > 0 else 'bold'),
                      ('\nuptime', DIM)),
        Text.assemble((format_span(v.down_s), f'bold {BAD}' if v.down_s else 'bold'), ('\ndowntime', DIM)),
        Text.assemble((f'{n:,}', f'bold {BAD}' if n else f'bold {OK}'), ('\ndrops', DIM)),
        Text.assemble((format_span(avg) if avg is not None else '—', f'bold {ACCENT}'), ('\navg drop', DIM)),
        Text.assemble((f'{sum(v.lat) / len(v.lat):.0f} ms' if v.lat else '—', 'bold'), ('\navg latency', DIM)),
    )
    sub = Text(f"{v.first:%b %d %H:%M} → {v.last:%b %d %H:%M} · {format_span(v.monitored)} monitored", style=DIM)
    return Panel(t, border_style=DIM, box=box.ROUNDED, padding=(0, 2), title=Text(f' {v.name} ', style='bold'),
                 title_align='left', subtitle=sub, subtitle_align='right')


def conn_lines(a):
    """One line per connection/network with its share of the time and drop count."""
    width = max(len(tab_title(n)) for n in a.by_tab)
    lines = []
    for name in sorted(a.by_tab, key=lambda k: -(a.by_tab[k]['up'] + a.by_tab[k]['down'])):
        c = a.by_tab[name]
        t = c['up'] + c['down']
        p = 100 * c['up'] / t if t > 0 else 0
        n = sum(1 for o in a.outages if o['tab'] == name)
        lines.append(Text.assemble(
            (f'  {tab_title(name):<{width}}  ', 'bold'), (f'{p:6.2f}% up', OK if p >= 99.9 else WARN if p >= 99 else BAD),
            (f' · {format_span(t)} · {n} drop{"" if n == 1 else "s"}', DIM), no_wrap=True, overflow='ellipsis'))
    return lines


def where(o):
    """Short description of the connection a drop happened on."""
    modem = ' (modem)' if o['modem'] else ''
    if o['tab'] == 'other':  # the tab name says nothing here, so say what it was
        return ('Wi-Fi, network name unknown' + modem) if o['raw'].endswith('-wifi') else o['raw']  # e.g. no-link
    return o['tab'] + modem


def drop_line(o, show_conn=True, selected=False):
    colour = CAUSE_COLOUR.get(o['cause'], DIM)
    secs = o['secs']
    line = Text.assemble((' ✗ ', f'bold {colour}'), (f"{o['cause'].lower():<9}", colour),
                         (f"{o['start']:%m-%d %H:%M:%S}  ", DIM),
                         (f'{format_span(secs):<8}', BAD if secs >= 60 else WARN if secs >= 15 else ''),
                         (where(o) if show_conn else '', DIM), no_wrap=True, overflow='ellipsis')
    if o['ongoing']:
        line.append('  ongoing', style=f'bold {BAD}')
    if selected:
        line.stylize('on grey23')
    return line


def print_rich_report(args, since, recent=15):
    a, msg = analyze(args, since)
    if a is None:
        console.print(Text(msg, style=DIM))
        return
    console.print()
    console.print(Text.assemble((' ◆ ', ACCENT), ('internet connection report', 'bold')))
    console.print(stat_cards(scope_view(a, None)))
    for line in conn_lines(a):
        console.print(line)
    if a.outages:
        upstream = sum(1 for o in a.outages if o['cause'] == 'UPSTREAM')
        local = sum(1 for o in a.outages if o['cause'] == 'LOCAL')
        console.print()
        console.print(Text(f' Most recent drops · {upstream} upstream (router OK), {local} local '
                           f'(router unreachable) in this period', style=DIM))
        for o in a.outages[-recent:]:
            console.print(drop_line(o))
    console.print()


MOUSE_ON = '\x1b[?1000h\x1b[?1006h'  # report wheel/clicks to us instead of scrolling the terminal
MOUSE_OFF = '\x1b[?1000l\x1b[?1006l'
SCROLL_STEP = 3


def parse_key(seq):
    """Name of a scroll key from the part of a CSI sequence after ESC [, else None."""
    if seq.startswith('<'):  # SGR mouse: <button;x;y then M/m
        try:
            button = int(seq[1:-1].split(';')[0])
        except ValueError:
            return None
        if seq[-1] == 'M' and button & 64:
            return 'wheelup' if button & 3 == 0 else 'wheeldown' if button & 3 == 1 else None
        if seq[-1] == 'M' and button == 0:  # left button pressed
            try:
                _, x, y = seq[1:-1].split(';')
                return ('click', int(x), int(y))
            except ValueError:
                return None
        return None
    return {'A': 'up', 'B': 'down', '5~': 'pgup', '6~': 'pgdn',
            'H': 'home', '1~': 'home', 'F': 'end', '4~': 'end'}.get(seq)


class InputWatcher:
    """Reads keys/mouse in a background thread so the drops list can be scrolled with the wheel or
    arrow keys and filtered by clicking. Turning on mouse reporting is also what stops the terminal
    scrolling away from the full-screen view."""

    def __init__(self, screen):
        self.screen = screen
        self.active = False
        self._pending = []
        self._restore = None

    def start(self):
        if not sys.stdin.isatty():
            return
        try:
            self._setup()
        except Exception:
            return
        self.active = True
        sys.stdout.write(MOUSE_ON)
        sys.stdout.flush()
        threading.Thread(target=self._run, daemon=True).start()

    def stop(self):
        if not self.active:
            return
        self.active = False
        sys.stdout.write(MOUSE_OFF)
        sys.stdout.flush()
        if self._restore:
            self._restore()

    def _setup(self):
        if os.name == 'nt':
            import ctypes
            from ctypes import wintypes
            k32 = ctypes.windll.kernel32
            k32.GetStdHandle.restype = wintypes.HANDLE
            self._h = k32.GetStdHandle(-10)  # STD_INPUT_HANDLE
            mode = wintypes.DWORD()
            if not k32.GetConsoleMode(self._h, ctypes.byref(mode)):
                raise OSError('stdin is not a console')
            # ENABLE_VIRTUAL_TERMINAL_INPUT: mouse and special keys arrive as ANSI sequences
            k32.SetConsoleMode(self._h, mode.value | 0x0200)
            self._restore = lambda: k32.SetConsoleMode(self._h, mode.value)
        else:
            import termios
            import tty
            fd = sys.stdin.fileno()
            old = termios.tcgetattr(fd)
            tty.setcbreak(fd)  # keeps Ctrl+C working
            self._restore = lambda: termios.tcsetattr(fd, termios.TCSADRAIN, old)

    def _read_char(self):
        if os.name != 'nt':
            return os.read(sys.stdin.fileno(), 1).decode('utf-8', 'ignore')
        import ctypes
        from ctypes import wintypes

        class KeyEvent(ctypes.Structure):
            _fields_ = [('down', wintypes.BOOL), ('repeat', wintypes.WORD), ('vk', wintypes.WORD),
                        ('scan', wintypes.WORD), ('char', wintypes.WCHAR), ('state', wintypes.DWORD)]

        class Union(ctypes.Union):
            _fields_ = [('key', KeyEvent), ('pad', ctypes.c_byte * 16)]

        class InputRecord(ctypes.Structure):
            _fields_ = [('type', wintypes.WORD), ('event', Union)]

        specials = {0x26: '\x1b[A', 0x28: '\x1b[B', 0x21: '\x1b[5~', 0x22: '\x1b[6~',
                    0x24: '\x1b[H', 0x23: '\x1b[F'}
        while not self._pending:
            rec, count = InputRecord(), wintypes.DWORD()
            if not ctypes.windll.kernel32.ReadConsoleInputW(self._h, ctypes.byref(rec), 1, ctypes.byref(count)):
                raise OSError('console read failed')
            if rec.type != 1 or not rec.event.key.down:  # KEY_EVENT key-down only
                continue
            key = rec.event.key
            if key.char != '\0':
                self._pending.append(key.char)
            elif key.vk in specials:
                self._pending.extend(specials[key.vk])
        return self._pending.pop(0)

    def _run(self):
        try:
            while self.active:
                ch = self._read_char()
                if ch == '\x1b':
                    if self._read_char() != '[':
                        continue
                    seq = ''
                    while True:
                        c = self._read_char()
                        seq += c
                        if '@' <= c <= '~':
                            break
                    key = parse_key(seq)
                    if isinstance(key, tuple):
                        self.screen.click(key[1], key[2])
                    elif key:
                        self.screen.scroll(key)
                elif ch in 'qQ':
                    _thread.interrupt_main()  # same as Ctrl+C: stop monitoring cleanly
                elif ch == '?':
                    self.screen.toggle_legend()
        except Exception:
            pass  # can't read input: the dashboard still works, just without scrolling


def tab_order(key):
    rank = {'ethernet': 0, 'other': 9}.get(key, 1)
    return rank, key.lower()


class Dashboard:
    """Full-screen view: live status and timelines, then one set of tabs (a tab per connection) that
    drives both the stat cards and the scrollable list of drops."""

    BAR_X0 = 11  # first screen column (1-based) of the timeline squares: ' ' + 9-char label
    NET_ROW, ROUTER_ROW = 3, 4  # screen rows (1-based) of the two timelines

    def __init__(self, monitor):
        self.m = monitor
        self.filter = None        # None = all connections, else a tab key
        self.manual_start = None  # first visible row once the user scrolls; None = follow the newest
        self.show_legend = True
        self.highlight = None     # start time of the drop picked by clicking the timeline
        self.jump = None          # timestamp of a timeline click, resolved to a drop on the next render
        self.tab_hits, self.tab_row = [], 0
        self.bar_w, self.width = 10, 80
        self.last_start, self.last_avail, self.last_total = 0, 1, 0

    # --- input
    def click(self, x, y):
        if y == self.tab_row:
            for x0, x1, key in self.tab_hits:
                if x0 <= x <= x1:
                    self.filter = None if key == self.filter else key
                    self.manual_start = self.highlight = self.jump = None
                    return
        elif y in (self.NET_ROW, self.ROUTER_ROW):
            m, n = self.m, self.bar_w
            cells = (m.hist_net if y == self.NET_ROW else m.hist_router)[-n:]
            tabs, stamps = m.hist_tab[-n:], m.hist_ts[-n:]
            i = x - self.BAR_X0
            if 0 <= i < min(len(cells), len(tabs), len(stamps)) and not cells[i]:  # a red/yellow square
                self.filter, self.jump, self.manual_start, self.highlight = tabs[i], stamps[i], None, None

    def scroll(self, key):
        if key == 'end':
            self.manual_start = None
            return
        base = self.last_start if self.manual_start is None else self.manual_start
        step = {'wheelup': -SCROLL_STEP, 'wheeldown': SCROLL_STEP, 'up': -1, 'down': 1,
                'pgup': -(self.last_avail - 1), 'pgdn': self.last_avail - 1}
        new = 0 if key == 'home' else base + step[key]
        self.manual_start = max(0, min(new, self.last_total - self.last_avail))

    def toggle_legend(self):
        self.show_legend = not self.show_legend

    # --- pieces
    def tabs(self, a):
        text = Text(no_wrap=True, overflow='ellipsis')
        hits = []
        text.append(' ')

        def item(key, name, colour, count):
            x0 = text.cell_len + 1
            if key == self.filter:  # selected tab: solid fill, count in an inset badge
                text.append(f' {name} ', style=f'bold grey7 on {colour}')
                text.append(f' {count:,} ', style=f'bold {colour} on grey19')
            else:                   # idle tab: raised chip, count in a darker badge
                text.append(f' {name} ', style=f'{colour} on grey23')
                text.append(f' {count:,} ', style='bold grey85 on grey30')
            hits.append((x0, text.cell_len, key))
            text.append(' ')

        item(None, 'All', 'grey85', len(a.outages))
        if len(a.by_tab) > 1:  # with a single connection a tab would just repeat "All"
            for key in sorted(a.by_tab, key=tab_order):
                item(key, tab_title(key), DIM if key == 'other' else ACCENT,
                     sum(1 for o in a.outages if o['tab'] == key))
            text.append('◂ click one to filter', style=DIM)
        self.tab_hits = hits
        return text

    @staticmethod
    def bar(name, hist, width, bad_colour):
        text = Text(f' {name:<9}', style=DIM, no_wrap=True)
        cells = hist[-width:]
        i = 0
        while i < len(cells):  # one append per run of identical cells
            j = i
            while j < len(cells) and cells[j] == cells[i]:
                j += 1
            text.append('■' * (j - i), style=OK if cells[i] else bad_colour)
            i = j
        return text

    def legend_lines(self, a, rows):
        """Explains only what is on screen: the causes and connections of the drops in `rows`, the colours
        of squares actually showing in the timelines, and the tabs that are displayed."""
        m, n = self.m, self.bar_w
        causes = {o['cause'] for o in rows}
        net_down = not all(m.hist_net[-n:])
        router_down = bool(m.router_ip) and not all(m.hist_router[-n:])
        lines = []

        by_cause = []
        if 'UPSTREAM' in causes:
            by_cause.append([('upstream', WARN), ("  router answered, the internet didn't → modem or provider", DIM)])
        if 'LOCAL' in causes:
            by_cause.append([('local', BAD), ("  router didn't answer → Wi-Fi, cable or router", DIM)])
        if 'unknown' in causes:
            by_cause.append([('unknown', DIM), ('  router status not known', DIM)])
        if by_cause:
            joined = [(' ', DIM)]
            for k, entry in enumerate(by_cause):
                joined += ([('     ', DIM)] if k else []) + entry
            if sum(cell_len(t) for t, _ in joined) < self.width:
                lines.append(joined)
            else:  # too wide to share a line
                lines.extend([(' ', DIM)] + entry for entry in by_cause)

        entries = []  # the squares: only the colours that are actually showing need a key
        if net_down:
            entries += [(' ■', BAD), (' internet down', DIM)]
        if router_down:
            entries += [('   ■' if entries else ' ■', WARN), (' router down', DIM)]
        if entries:
            entries += [('      click a red/yellow ■ above to jump to that drop', DIM)]
            lines.append(entries)

        if any(o['modem'] for o in rows):
            lines.append([(' (modem) = plugged straight into a modem rather than a router (guessed from the IP)', DIM)])
        return [Text.assemble(*e, no_wrap=True, overflow='ellipsis') for e in lines]

    def __rich_console__(self, console, options):
        m = self.m
        a = m.stats
        width = options.max_width
        height = options.height or console.size.height
        now = datetime.now()

        self.width = width
        self.bar_w = bar_w = max(10, width - 14)
        router = f'router {m.router_ip}' if m.router_ip else 'no router found'
        head = [Text.assemble((' ◆ ', ACCENT), ('internet monitor', 'bold'),
                              (f'  · {label(m.conn, m.network)} · {router}'
                               f'  · bars: last {format_span(bar_w * m.a.interval)}', DIM),
                              no_wrap=True, overflow='ellipsis')]
        if m.prev is None:
            head.append(Text.assemble((' ● ', f'bold {ACCENT}'), ('checking…', DIM)))
        elif m.prev:
            head.append(Text.assemble((' ● ', f'bold {OK}'), ('ONLINE', f'bold {OK}'),
                                      (f'   since {m.state_since:%H:%M:%S} · {m.last_ms} ms'
                                       f' · last check {m.last_check:%H:%M:%S}', DIM), no_wrap=True))
        else:
            head.append(Text.assemble((' ● ', f'bold {BAD}'),
                                      (f'OFFLINE for {format_span((now - m.state_since).total_seconds())}', f'bold {BAD}'),
                                      (f'   since {m.state_since:%H:%M:%S}', DIM), no_wrap=True))
        head.append(self.bar('Internet', m.hist_net, bar_w, BAD))
        head.append(self.bar('Router', m.hist_router, bar_w, WARN) if m.router_ip else Text(''))
        yield from head

        if a is None:
            yield Text(f' {m.stats_msg}', style=DIM)
            return
        if self.filter is not None and self.filter not in a.by_tab:
            self.filter = None  # that connection has no data in this period
        yield stat_cards(scope_view(a, self.filter))  # border, two lines of numbers/labels, border: 4 rows

        self.tab_row = len(head) + 4 + 1  # 1-based screen row of the tab strip
        yield self.tabs(a)

        vis = a.outages if self.filter is None else [o for o in a.outages if o['tab'] == self.filter]
        n = len(vis)
        show_legend = self.show_legend and height >= 22
        # Reserve room for the most the legend could say about this tab, so the list doesn't jump while scrolling.
        reserve = len(self.legend_lines(a, vis)) if show_legend else 0
        avail = max(1, height - self.tab_row - 1 - reserve - 1)  # minus list header, legend and the rule
        if self.jump is not None:  # a timeline click: bring that drop into view and highlight it
            for i, o in enumerate(vis):
                slack = timedelta(seconds=m.a.interval)
                if o['start'] - slack <= self.jump <= o['end'] + slack:
                    self.highlight = o['start']
                    self.manual_start = max(0, min(i - avail // 2, n - avail))
                    self.jump = None
                    break
            else:
                if (now - self.jump).total_seconds() > 120:
                    self.jump = None  # never turned into a drop; give up
        start = max(0, n - avail)
        if self.manual_start is not None:
            start = max(0, min(self.manual_start, n - avail))
        self.last_start, self.last_avail, self.last_total = start, avail, n
        window = vis[start:start + avail]
        legend = self.legend_lines(a, window) if show_legend else []

        show_conn = self.filter in (None, 'other')  # elsewhere the tab already says it
        yield Text(f"   {'cause':<9}{'when':<16}{'length':<8}{'connection' if show_conn else ''}", style=DIM,
                   no_wrap=True)
        for o in window:
            yield drop_line(o, show_conn, selected=o['start'] == self.highlight)
        if not n:
            yield Text('  ✓ no drops in this period' if self.filter is None else '  no drops on this connection',
                       style=OK if self.filter is None else DIM)
        for _ in range(avail - len(window) - (0 if n else 1)):
            yield Text('')
        for _ in range(reserve - len(legend)):
            yield Text('')  # the legend has less to say about what's showing right now
        yield from legend

        left = f'drops {start + 1 if n else 0}–{start + len(window)} of {n}'
        right = (('End to follow' if self.manual_start is not None else 'wheel/↑↓ scroll')
                 + ' · ? legend · q quits')
        fill = width - cell_len(left) - cell_len(right) - 4
        if fill >= 3:
            line = '─' * (fill + 1)
            yield Text(f'{left} {line} {right} ', style=DIM, no_wrap=True)
        else:
            yield Rule(Text(f'{left} · {right}', style=DIM), style=DIM, align='left')


# ---------------------------------------------------------------- monitor

class Monitor:
    HIST = 600  # checks of history kept for the timelines

    def __init__(self, args):
        self.a = args
        self.router_ip = args.router_ip or default_route()[0]
        try:
            self.bar_width = max(10, min(60, shutil.get_terminal_size().columns - 16))
        except Exception:
            self.bar_width = 60
        self.hist_net, self.hist_router = [], []
        self.hist_tab, self.hist_ts = [], []  # per check: which tab it belongs to, and when (for timeline clicks)
        self.prev = None
        self.state_since = self.last_check = datetime.now()
        self.last_ms = 0
        self.conn, self.network = 'unknown', ''
        self.stats, self.stats_msg = None, 'Collecting data…'

    # --- plain (no rich) display
    def bar(self, name, hist, bad_color):
        cells = ''.join(color(SQUARE, 'green' if ok else bad_color) for ok in hist[-self.bar_width:])
        return f'{name:<10}{cells}'

    def live_lines(self):
        a = self.a
        span = format_span(self.bar_width * a.interval)
        lines = [color(f'Internet monitor - Ctrl+C to stop   (bars: last {span})', 'cyan')]
        if self.prev:
            lines.append(color(f'ONLINE  since {self.state_since:%H:%M:%S}  (last check {self.last_check:%H:%M:%S}, '
                               f'{self.last_ms} ms)   via {label(self.conn, self.network)}', 'green'))
        else:
            lines.append(color(f'OFFLINE for {format_span((self.last_check - self.state_since).total_seconds())}  '
                               f'(since {self.state_since:%H:%M:%S})   via {label(self.conn, self.network)}', 'red'))
        lines.append(self.bar('Internet', self.hist_net, 'red'))
        lines.append(self.bar('Router', self.hist_router, 'yellow') if self.router_ip else '')
        return lines

    def draw_live(self):
        sys.stdout.write('\033[H' + ''.join(f'{l}\033[K\n' for l in self.live_lines()))
        sys.stdout.flush()

    def since(self):
        a = self.a
        return parse_since(a.since) if a.since else datetime.now() - timedelta(hours=a.dashboard_hours)

    def draw_dashboard(self):
        height = shutil.get_terminal_size().lines - 1
        sys.stdout.write('\033[2J\033[H')
        for l in self.live_lines():
            print(l)
        print()
        print_lines(build_report(self.a, self.since(), recent=5), limit=max(0, height - 5))
        sys.stdout.flush()

    # --- logging
    def log(self, ts, up, ms, router):
        append_row(self.a.log_file, [f'{ts:{TS_FORMAT}}', 'UP' if up else 'DOWN', '' if ms is None else ms,
                                     router, self.conn, self.network])

    def print_summary(self):
        """After a rich dashboard session: leave the stats in the normal scrollback."""
        if not self.rich:
            return
        self.refresh_stats()
        if self.stats:
            console.print()
            console.print(stat_cards(self.stats))
            console.print(Text(f'  ↳ log  {os.path.abspath(self.a.log_file)}', style=DIM))

    def refresh_stats(self):
        self.stats, self.stats_msg = analyze(self.a, self.since())

    def run(self):
        a = self.a
        path = Path(a.log_file)
        if not path.exists():
            path.write_text(HEADER + '\n')
        else:
            backup = upgrade_log(path)  # older log without the Network column
            if backup:
                print(f'Upgraded {path} with a Network column. Original saved as {backup}')
        if a.quiet:
            router = f' + router {self.router_ip}' if self.router_ip else ' (no router found)'
            print(color(f"Monitoring {', '.join(a.targets)}{router} every {a.interval}s. Logging to {path}. "
                        'Ctrl+C to stop.', 'cyan'))

        self.rich = HAVE_RICH and not a.plain and not a.quiet and sys.stdout.isatty()
        self.conn, self.network = connection()
        last_conn_check = datetime.now()
        logged_router = logged_conn = logged_network = None
        last_write = datetime.min
        last_redraw = datetime.min
        n = 0
        wrote_any = False
        live = watcher = None
        if self.rich:
            dash = Dashboard(self)
            live = Live(dash, console=console, screen=True, refresh_per_second=10)
            watcher = InputWatcher(dash)
            live.start()
            watcher.start()
        try:
            while True:
                t0 = time.monotonic()
                now = datetime.now()  # stamp the check when it STARTS: a failed check can take several seconds to time out
                ms = next((r for r in (ping(h, a.timeout) for h in a.targets) if r is not None), None)
                router = ''
                if self.router_ip:
                    router = 'UP' if ping(self.router_ip, a.timeout) is not None else 'DOWN'
                up = ms is not None
                if not up or (now - last_conn_check).total_seconds() >= 15:
                    self.conn, self.network = connection()
                    last_conn_check = now

                # Log only when something changed, plus a periodic "still alive" row.
                changed = up != self.prev
                log_row = (changed or router != logged_router or self.conn != logged_conn
                           or self.network != logged_network
                           or (now - last_write).total_seconds() >= a.heartbeat)
                if log_row:
                    self.log(now, up, ms, router)
                    last_write, logged_router, logged_conn, logged_network, wrote_any = (
                        now, router, self.conn, self.network, True)

                if changed:
                    if a.quiet:
                        if up and self.prev is False:
                            print(color(f'{now:%H:%M:%S}  BACK UP after '
                                        f'{format_span((now - self.state_since).total_seconds())}', 'green'))
                        elif not up:
                            why = {'UP': 'router OK -> upstream (modem/ISP)',
                                   'DOWN': 'router unreachable -> local'}.get(router, '')
                            print(color(f'{now:%H:%M:%S}  CONNECTION DOWN  {why}', 'red'))
                    self.state_since = now
                self.prev, self.last_check, self.last_ms = up, now, ms

                self.hist_net = (self.hist_net + [up])[-self.HIST:]
                self.hist_router = (self.hist_router + [router != 'DOWN'])[-self.HIST:]
                self.hist_tab = (self.hist_tab + [tab_key(self.conn, self.network)])[-self.HIST:]
                self.hist_ts = (self.hist_ts + [now])[-self.HIST:]

                # Re-read the log for the stats on a log row or every 30s; the rich view repaints by itself.
                if self.rich:
                    if log_row or (now - last_redraw).total_seconds() >= 30:
                        self.refresh_stats()
                        last_redraw = now
                elif not a.quiet:
                    if log_row or (now - last_redraw).total_seconds() >= 30:
                        self.draw_dashboard()
                        last_redraw = now
                    else:
                        self.draw_live()

                n += 1
                if a.count and n >= a.count:
                    break
                time.sleep(max(0, a.interval - (time.monotonic() - t0)))
        finally:
            if watcher:
                watcher.stop()
            if live:
                live.stop()
            if wrote_any:
                append_row(a.log_file, [f'{datetime.now():{TS_FORMAT}}', 'STOP', '', '', '', ''])


# ---------------------------------------------------------------- self-update

UPDATE_REPO = 'tvanc/connection-monitor'
UPDATE_BRANCH = 'main'
UPDATE_FILES = ('main.py', 'start.command', 'start.bat')  # replaced only if they already exist next to the script


def http_get(url, timeout=4):
    req = urllib.request.Request(url, headers={'User-Agent': 'connection-monitor-updater',
                                               'Accept': 'application/vnd.github.sha'})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def latest_commit():
    """SHA of the newest commit on the update branch, or None."""
    url = os.environ.get('CM_UPDATE_API') or f'https://api.github.com/repos/{UPDATE_REPO}/commits/{UPDATE_BRANCH}'
    text = http_get(url).decode().strip()
    if text.startswith('{'):
        text = json.loads(text).get('sha', '')
    return text if re.fullmatch(r'[0-9a-f]{40}', text) else None


def self_update(args):
    """Install the newest version from GitHub and restart, if this is a plain copy and GitHub is ahead.
    Silent on any failure (offline, rate limited...): the version you have keeps working."""
    if args.no_update or os.environ.get('CONNECTION_MONITOR_NO_UPDATE') or os.environ.get('CM_JUST_UPDATED'):
        return
    here = Path(__file__).resolve().parent
    if (here / '.git').exists():
        return  # a development checkout: never overwrite it
    try:
        # A socket timeout doesn't cover a DNS lookup that hangs when there's no internet, so the first request
        # runs in a thread we only wait a few seconds for: being offline must not hold up start-up.
        found = []

        def check():
            try:
                found.append(latest_commit())
            except Exception:
                pass

        checker = threading.Thread(target=check, daemon=True)
        checker.start()
        checker.join(5)
        sha = found[0] if found and not checker.is_alive() else None
        marker = here / '.version'  # the commit this copy was last brought up to date with
        if not sha or (marker.exists() and marker.read_text().strip() == sha):
            return
        raw = os.environ.get('CM_UPDATE_RAW') or f'https://raw.githubusercontent.com/{UPDATE_REPO}'
        new = {name: http_get(f'{raw}/{sha}/{name}') for name in UPDATE_FILES
               if name == 'main.py' or (here / name).exists()}
        compile(new['main.py'], 'main.py', 'exec')  # refuse to install something that doesn't even compile
        same = lambda a, b: a.replace(b'\r\n', b'\n') == b.replace(b'\r\n', b'\n')  # ignore line-ending differences
        changed = [n for n, data in new.items() if not (here / n).exists() or not same((here / n).read_bytes(), data)]
        for name in changed:
            target = here / name
            tmp = target.with_name(target.name + '.new')
            tmp.write_bytes(new[name])
            if target.exists():
                shutil.copymode(target, tmp)  # keeps start.command executable
                if name == 'main.py':
                    shutil.copy2(target, target.with_name('main.py.previous'))  # one step back, just in case
            os.replace(tmp, target)  # replacing (not editing) is safe even while a shell is running start.command
        marker.write_text(sha + '\n')
        if changed:
            print(f'Updated to the latest version ({sha[:7]}); restarting...')
            os.environ['CM_JUST_UPDATED'] = '1'
            sys.stdout.flush()
            os.execv(sys.executable, [sys.executable] + sys.argv)
    except Exception:
        pass


def main():
    p = argparse.ArgumentParser(description='Monitor internet connectivity and report uptime and drops.')
    p.add_argument('--report', action='store_true', help='show stats from the log and exit')
    p.add_argument('--compact', action='store_true',
                   help='convert an older per-check log to the change-only format (keeps a .bak backup)')
    p.add_argument('--upgrade', action='store_true',
                   help='add the Network column to an older log (existing Wi-Fi rows get "unknown"; keeps a .bak)')
    p.add_argument('--targets', nargs='+', default=['1.1.1.1', '8.8.8.8', '9.9.9.9'])
    p.add_argument('--router-ip', help='default: auto-detected default gateway')
    p.add_argument('--interval', type=int, default=5, help='seconds between checks')
    p.add_argument('--timeout', type=int, default=2000, help='ping timeout in ms')
    p.add_argument('--heartbeat', type=int, default=300, help='how often an unchanged state is re-logged (s)')
    p.add_argument('--log-file', default=str(Path(__file__).resolve().parent / 'internet-log.csv'))
    p.add_argument('--since', help="report start: '24h', '7d', or an ISO date/time")
    p.add_argument('--dashboard-hours', type=int, default=24,
                   help='live dashboard stats cover this many hours (unless --since is given)')
    p.add_argument('--allow-sleep', action='store_true', help="don't keep the computer awake while monitoring")
    p.add_argument('--quiet', action='store_true', help='no live dashboard, just print up/down events')
    p.add_argument('--wifi-shortcut', default=SHORTCUT_NAME, metavar='NAME',
                   help='macOS only: name of a Shortcut that returns the Wi-Fi network name (default "%(default)s")')
    p.add_argument('--no-update', action='store_true',
                   help="don't check GitHub for a newer version on start-up")
    p.add_argument('--plain', action='store_true', help="simple text output even if 'rich' is installed")
    p.add_argument('--count', type=int, default=0, help='stop after N checks (0 = run forever)')
    args = p.parse_args()
    globals()['SHORTCUT_NAME'] = args.wifi_shortcut
    self_update(args)

    if os.name == 'nt':
        os.system('')  # enables ANSI escape codes in the Windows console
    if args.upgrade:
        backup = upgrade_log(args.log_file)
        print(f'Upgraded {args.log_file}. Original saved as {backup}' if backup else 'Nothing to upgrade.')
        return
    if args.compact:
        compact(args)
        return
    if args.report:
        since = parse_since(args.since)
        if HAVE_RICH and sys.stdout.isatty() and not args.plain:
            print_rich_report(args, since)
        else:
            print_lines(build_report(args, since))
        return

    # Make sure the STOP row gets written when the terminal closes or the process is terminated.
    for sig in (signal.SIGTERM, getattr(signal, 'SIGHUP', None)):
        if sig:
            signal.signal(sig, lambda *_: sys.exit(0))
    release = (lambda: None) if args.allow_sleep else keep_awake()
    monitor = Monitor(args)
    try:
        monitor.run()
    except KeyboardInterrupt:
        pass
    finally:
        release()
    if getattr(monitor, 'rich', False):
        monitor.print_summary()
    print(f'\nStopped. Log: {args.log_file}')
    if not HAVE_RICH and sys.stdout.isatty():
        print('Tip: pip3 install rich for the full-screen dashboard.')


if __name__ == '__main__':
    main()
