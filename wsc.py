#!/usr/bin/env python3
"""wsc — 윈도우 자원 사용량 터미널 모니터 (windows system check).

표준 라이브러리만 사용한다. 외부 패키지 설치 불필요.
프로세스 정보는 작업 관리자와 같은 길(NtQuerySystemInformation)로 한 번에 읽는다.
tasklist·wmic·netstat 같은 외부 명령을 띄우지 않아 가볍고, 윈도우 표시 언어에 따라
출력 글자가 바뀌어 읽기가 깨지는 일도 없다.
"""

import argparse
import collections
import ctypes
import os
import re
import signal
import struct
import sys
import tempfile
import time
import threading
import unicodedata
import urllib.error
import urllib.request

if sys.platform != "win32":
    sys.exit("wsc 는 윈도우 전용이다. 맥이라면 msc 를 써라: https://github.com/seeminglyjs/msc")

import msvcrt  # noqa: E402  윈도우에만 있는 모듈이라 위의 검사 뒤에 불러온다
import winreg  # noqa: E402
from ctypes import wintypes  # noqa: E402

VERSION = "1.1.0"
RAW_URL = "https://raw.githubusercontent.com/seeminglyjs/wsc/main/wsc.py"
REPO_URL = "https://github.com/seeminglyjs/wsc"

INTERVAL_MIN = 0.5
INTERVAL_MAX = 10.0
KEY_POLL = 0.03  # 키 입력을 살피는 간격(초). 윈도우 select 는 콘솔 입력을 못 기다린다

# ── ANSI 제어 문자 ──────────────────────────────────────────────
ESC = "\x1b"
ALT_SCREEN_ON = f"{ESC}[?1049h"
ALT_SCREEN_OFF = f"{ESC}[?1049l"
CURSOR_HIDE = f"{ESC}[?25l"
CURSOR_SHOW = f"{ESC}[?25h"
CURSOR_HOME = f"{ESC}[H"
CLEAR_LINE = f"{ESC}[K"
CLEAR_BELOW = f"{ESC}[J"

RESET = f"{ESC}[0m"
BOLD = f"{ESC}[1m"
DIM = f"{ESC}[2m"
GREEN = f"{ESC}[38;5;40m"
YELLOW = f"{ESC}[38;5;220m"
RED = f"{ESC}[38;5;203m"
BLUE = f"{ESC}[38;5;75m"
CYAN = f"{ESC}[38;5;80m"
GRAY = f"{ESC}[38;5;244m"
HEADER_BG = f"{ESC}[48;5;238m{ESC}[38;5;255m"
GRAY_ON_HEADER = f"{ESC}[22m{ESC}[38;5;250m"
LOGO_ON_HEADER = f"{ESC}[1m{ESC}[38;5;80m"
# 고른 줄은 글자를 흰색 하나로 통일한다. 파란 바탕 위에 회색·초록 숫자는 잘 안 읽힌다
SELECT_BG = f"{ESC}[48;5;24m{ESC}[38;5;255m"
DANGER_BG = f"{ESC}[48;5;88m{ESC}[38;5;255m"
# 압박 표시는 글자가 아니라 색 배지로 둔다. 평소엔 눈에 안 걸리고, 바뀌면 바로 보이게
PRESSURE_BADGE = {
    "여유": f"{ESC}[48;5;28m{ESC}[38;5;255m",
    "주의": f"{ESC}[48;5;178m{ESC}[38;5;232m",
    "위험": DANGER_BG,
}
# 맨 아래 조작 줄. 누르는 키는 자판처럼 밝게 도드라지고, 설명글은 차분하게 깔린다
FOOTER_BG = f"{ESC}[48;5;236m{ESC}[38;5;250m"
FOOTER_TEXT = f"{ESC}[22m{ESC}[38;5;250m"
FOOTER_ON = f"{ESC}[1m{ESC}[38;5;80m"
KEY_BG = f"{ESC}[48;5;252m{ESC}[38;5;232m"

# 종료를 막을 프로세스. 죽이면 블루스크린이 뜨거나 곧바로 로그아웃·재시동된다.
# 윈도우는 대소문자를 가리지 않으므로 소문자로 비교한다
PROTECTED_NAMES = {
    "system", "registry", "memory compression", "secure system",
    "smss.exe", "csrss.exe", "wininit.exe", "winlogon.exe",
    "services.exe", "lsass.exe", "lsaiso.exe",
}
PROTECTED_PIDS = {0, 4}  # 0 은 유휴 프로세스, 4 는 커널(System)

BLOCKS = "▏▎▍▌▋▊▉█"
SPARKS = "▁▂▃▄▅▆▇█"
SPARK_LEN = 20  # CPU 추이로 보여줄 최근 갱신 횟수

# 옛 콘솔(conhost)을 한중일 코드 페이지로 쓰면 █ · … 같은 '폭이 애매한' 글자를
# 두 칸으로 그려서 표가 통째로 어긋난다. 그럴 때 한 칸짜리 영문 기호로 바꿔 그린다
ASCII_MAP = str.maketrans({
    "█": "#", "·": ".", "…": "~", "–": "-", "—": "-",
    "›": ">", "↑": "^", "↓": "v", "▼": "v",
    "▁": "_", "▂": ".", "▃": ":", "▄": "-", "▅": "=", "▆": "+", "▇": "*",
})
USE_ASCII = False


# ── 문자열 폭 계산 (한글·CJK 는 두 칸 차지) ────────────────────
def dwidth(s: str) -> int:
    total = 0
    for ch in s:
        if unicodedata.combining(ch):
            continue
        total += 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
    return total


def dtrunc(s: str, width: int) -> str:
    """표시 폭 기준으로 자른다. 잘린 경우 끝에 … 를 붙인다."""
    if dwidth(s) <= width:
        return s
    out, used = [], 0
    for ch in s:
        w = 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
        if used + w > width - 1:
            break
        out.append(ch)
        used += w
    return "".join(out) + "…"


def dpad(s: str, width: int) -> str:
    """표시 폭 기준 왼쪽 정렬 패딩."""
    s = dtrunc(s, width)
    return s + " " * max(0, width - dwidth(s))


def rpad(s: str, width: int) -> str:
    """표시 폭 기준 오른쪽 정렬 패딩."""
    s = dtrunc(s, width)
    return " " * max(0, width - dwidth(s)) + s


# ── 윈도우 API 연결 ─────────────────────────────────────────────
ntdll = ctypes.WinDLL("ntdll")
kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
user32 = ctypes.WinDLL("user32", use_last_error=True)
iphlpapi = ctypes.WinDLL("iphlpapi")


class UNICODE_STRING(ctypes.Structure):
    _fields_ = [
        ("Length", wintypes.USHORT),  # 바이트 수. 글자 수가 아니다
        ("MaximumLength", wintypes.USHORT),
        ("Buffer", ctypes.c_void_p),
    ]


class SYSTEM_PROCESS_INFORMATION(ctypes.Structure):
    # 필드 순서와 크기는 윈도우 내부 구조 그대로다. 줄 하나라도 빠지면 뒤가 다 어긋난다
    _fields_ = [
        ("NextEntryOffset", wintypes.ULONG),
        ("NumberOfThreads", wintypes.ULONG),
        ("WorkingSetPrivateSize", ctypes.c_longlong),
        ("HardFaultCount", wintypes.ULONG),
        ("NumberOfThreadsHighWatermark", wintypes.ULONG),
        ("CycleTime", ctypes.c_ulonglong),
        ("CreateTime", ctypes.c_longlong),
        ("UserTime", ctypes.c_longlong),  # 100ns 단위
        ("KernelTime", ctypes.c_longlong),
        ("ImageName", UNICODE_STRING),
        ("BasePriority", ctypes.c_long),
        ("UniqueProcessId", ctypes.c_void_p),
        ("InheritedFromUniqueProcessId", ctypes.c_void_p),
        ("HandleCount", wintypes.ULONG),
        ("SessionId", wintypes.ULONG),
        ("UniqueProcessKey", ctypes.c_void_p),
        ("PeakVirtualSize", ctypes.c_size_t),
        ("VirtualSize", ctypes.c_size_t),
        ("PageFaultCount", wintypes.ULONG),
        ("PeakWorkingSetSize", ctypes.c_size_t),
        ("WorkingSetSize", ctypes.c_size_t),
        ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
        ("QuotaPagedPoolUsage", ctypes.c_size_t),
        ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
        ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
        ("PagefileUsage", ctypes.c_size_t),
        ("PeakPagefileUsage", ctypes.c_size_t),
        ("PrivatePageCount", ctypes.c_size_t),
    ]


class SYSTEM_PAGEFILE_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("NextEntryOffset", wintypes.ULONG),
        ("TotalSize", wintypes.ULONG),  # 페이지 수
        ("TotalInUse", wintypes.ULONG),
        ("PeakUsage", wintypes.ULONG),
        ("PageFileName", UNICODE_STRING),
    ]


class MEMORYSTATUSEX(ctypes.Structure):
    _fields_ = [
        ("dwLength", wintypes.DWORD),
        ("dwMemoryLoad", wintypes.DWORD),
        ("ullTotalPhys", ctypes.c_ulonglong),
        ("ullAvailPhys", ctypes.c_ulonglong),
        ("ullTotalPageFile", ctypes.c_ulonglong),
        ("ullAvailPageFile", ctypes.c_ulonglong),
        ("ullTotalVirtual", ctypes.c_ulonglong),
        ("ullAvailVirtual", ctypes.c_ulonglong),
        ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
    ]


class PERFORMANCE_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("cb", wintypes.DWORD),
        ("CommitTotal", ctypes.c_size_t),  # 여기부터 PageSize 까지 페이지 수
        ("CommitLimit", ctypes.c_size_t),
        ("CommitPeak", ctypes.c_size_t),
        ("PhysicalTotal", ctypes.c_size_t),
        ("PhysicalAvailable", ctypes.c_size_t),
        ("SystemCache", ctypes.c_size_t),
        ("KernelTotal", ctypes.c_size_t),
        ("KernelPaged", ctypes.c_size_t),
        ("KernelNonpaged", ctypes.c_size_t),
        ("PageSize", ctypes.c_size_t),
        ("HandleCount", wintypes.DWORD),
        ("ProcessCount", wintypes.DWORD),
        ("ThreadCount", wintypes.DWORD),
    ]


ntdll.NtQuerySystemInformation.argtypes = [
    wintypes.ULONG, ctypes.c_void_p, wintypes.ULONG, ctypes.POINTER(wintypes.ULONG)
]
ntdll.NtQuerySystemInformation.restype = ctypes.c_long
kernel32.GetSystemTimes.argtypes = [ctypes.POINTER(wintypes.FILETIME)] * 3
kernel32.GetSystemTimes.restype = wintypes.BOOL
kernel32.GlobalMemoryStatusEx.argtypes = [ctypes.POINTER(MEMORYSTATUSEX)]
kernel32.GlobalMemoryStatusEx.restype = wintypes.BOOL
kernel32.K32GetPerformanceInfo.argtypes = [
    ctypes.POINTER(PERFORMANCE_INFORMATION), wintypes.DWORD
]
kernel32.K32GetPerformanceInfo.restype = wintypes.BOOL
kernel32.GetStdHandle.argtypes = [wintypes.DWORD]
kernel32.GetStdHandle.restype = wintypes.HANDLE
kernel32.GetConsoleMode.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
kernel32.GetConsoleMode.restype = wintypes.BOOL
kernel32.SetConsoleMode.argtypes = [wintypes.HANDLE, wintypes.DWORD]
kernel32.SetConsoleMode.restype = wintypes.BOOL
kernel32.GetConsoleOutputCP.restype = wintypes.UINT
kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
kernel32.OpenProcess.restype = wintypes.HANDLE
kernel32.TerminateProcess.argtypes = [wintypes.HANDLE, wintypes.UINT]
kernel32.TerminateProcess.restype = wintypes.BOOL
kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
kernel32.CloseHandle.restype = wintypes.BOOL
iphlpapi.GetExtendedTcpTable.argtypes = [
    ctypes.c_void_p, ctypes.POINTER(wintypes.DWORD), wintypes.BOOL,
    wintypes.ULONG, ctypes.c_int, wintypes.ULONG,
]
iphlpapi.GetExtendedTcpTable.restype = wintypes.DWORD

WNDENUMPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
user32.EnumWindows.argtypes = [WNDENUMPROC, wintypes.LPARAM]
user32.EnumWindows.restype = wintypes.BOOL
user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
user32.GetWindowThreadProcessId.restype = wintypes.DWORD
user32.IsWindowVisible.argtypes = [wintypes.HWND]
user32.IsWindowVisible.restype = wintypes.BOOL
user32.GetWindow.argtypes = [wintypes.HWND, wintypes.UINT]
user32.GetWindow.restype = wintypes.HWND
user32.PostMessageW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
user32.PostMessageW.restype = wintypes.BOOL

STATUS_INFO_LENGTH_MISMATCH = ctypes.c_long(0xC0000004).value
SYSTEM_PROCESS_INFO = 5
SYSTEM_PAGEFILE_INFO = 18
ERROR_ACCESS_DENIED = 5
ERROR_INVALID_PARAMETER = 87
ERROR_INSUFFICIENT_BUFFER = 122
PROCESS_TERMINATE = 0x0001
WM_CLOSE = 0x0010
GW_OWNER = 4
AF_INET, AF_INET6 = 2, 23
TCP_TABLE_OWNER_PID_LISTENER = 3
ENABLE_VIRTUAL_TERMINAL_PROCESSING = 0x0004
STD_OUTPUT_HANDLE = -11 & 0xFFFFFFFF


def query_system(info_class: int, size: int):
    """NtQuerySystemInformation 을 부른다. 버퍼가 모자라면 늘려서 다시 부른다.

    (버퍼, 맞았던 크기) 를 돌려준다. 실패하면 버퍼 자리에 None.
    """
    for _ in range(8):
        buf = ctypes.create_string_buffer(size)
        needed = wintypes.ULONG(0)
        status = ntdll.NtQuerySystemInformation(
            info_class, buf, size, ctypes.byref(needed)
        )
        if status == STATUS_INFO_LENGTH_MISMATCH:
            # 두 번 부르는 사이에도 프로세스가 생기므로 알려준 크기보다 넉넉히 잡는다
            size = max(size * 2, needed.value + 64 * 1024)
            continue
        return (buf if status >= 0 else None), size
    return None, size


def read_unicode(us: UNICODE_STRING) -> str:
    if not us.Buffer or not us.Length:
        return ""
    return ctypes.wstring_at(us.Buffer, us.Length // 2)


# ── 시스템 정보 수집 ────────────────────────────────────────────
def cpu_brand() -> str:
    """레지스트리의 CPU 이름에서 (R)·(TM)·클럭 같은 군더더기를 걷어낸다."""
    try:
        with winreg.OpenKey(
            winreg.HKEY_LOCAL_MACHINE,
            r"HARDWARE\DESCRIPTION\System\CentralProcessor\0",
        ) as key:
            raw = str(winreg.QueryValueEx(key, "ProcessorNameString")[0])
    except OSError:
        return "CPU"
    raw = raw.strip()  # 레지스트리 값 끝에 공백이 잔뜩 붙어 있는 경우가 흔하다
    raw = re.sub(r"\((?:R|TM)\)", "", raw, flags=re.I)
    raw = re.sub(r"\s+CPU\s+@.*$", "", raw)
    raw = re.sub(r"\s+\d+-Core Processor$", "", raw)
    return " ".join(raw.split()) or "CPU"


def is_admin() -> bool:
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


NCPU = os.cpu_count() or 1
CPU_BRAND = cpu_brand()
IS_ADMIN = is_admin()
_proc_buf_size = 512 * 1024  # 지난번에 맞았던 크기를 기억해 두면 다시 부르는 일이 줄어든다


def sample_processes() -> dict:
    """{pid: (생성 시각, 누적 CPU 초, 개인 작업 집합, 작업 집합, 이름)} 스냅샷.

    한 번 호출로 모든 프로세스가 나온다. 프로세스를 하나씩 여는 방식과 달리
    관리자 권한이 없어도 시스템·다른 사용자 프로세스까지 다 보인다.
    """
    global _proc_buf_size
    buf, _proc_buf_size = query_system(SYSTEM_PROCESS_INFO, _proc_buf_size)
    if buf is None:
        return {}

    procs = {}
    offset = 0
    while True:
        info = SYSTEM_PROCESS_INFORMATION.from_buffer(buf, offset)
        pid = info.UniqueProcessId or 0
        # PID 0 은 '유휴 프로세스'. 일한 시간이 아니라 논 시간이라 표에 넣지 않는다
        if pid:
            name = read_unicode(info.ImageName) or ("System" if pid == 4 else f"PID {pid}")
            procs[pid] = (
                info.CreateTime,
                (info.UserTime + info.KernelTime) / 1e7,
                max(0, info.WorkingSetPrivateSize),
                info.WorkingSetSize,
                name,
            )
        if not info.NextEntryOffset:
            break
        offset += info.NextEntryOffset
    return procs


def system_times():
    """(유휴, 커널, 사용자) 누적 시간. 커널 시간에는 유휴 시간이 들어 있다."""
    idle, kern, user = wintypes.FILETIME(), wintypes.FILETIME(), wintypes.FILETIME()
    if not kernel32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kern), ctypes.byref(user)):
        return None

    def value(ft):
        return (ft.dwHighDateTime << 32) | ft.dwLowDateTime

    return value(idle), value(kern), value(user)


def _tcp_listeners(family: int):
    size = wintypes.DWORD(16 * 1024)
    for _ in range(5):
        buf = ctypes.create_string_buffer(size.value)
        ret = iphlpapi.GetExtendedTcpTable(
            buf, ctypes.byref(size), False, family, TCP_TABLE_OWNER_PID_LISTENER, 0
        )
        if ret == 0:
            return buf
        if ret != ERROR_INSUFFICIENT_BUFFER:
            return None
    return None


def sample_ports() -> dict:
    """{PID: [포트, ...]} — 그 프로세스가 연결을 기다리며 잡고 있는 TCP 포트.

    윈도우는 관리자 권한이 없어도 어느 프로세스가 잡은 포트인지 다 알려준다.
    netstat 을 띄워 읽지 않는 이유는, 한국어 윈도우 등에서 상태 글자가 번역되어
    나오는 경우가 있어 읽는 쪽이 깨지기 때문이다.
    """
    found = {}
    # 표 한 줄의 모양. 포트는 세 번째 칸, 주인 PID 는 마지막 칸이다
    layouts = ((AF_INET, "<6I", 2, 5), (AF_INET6, "<16sII16sIIII", 2, 7))
    for family, row_fmt, port_at, pid_at in layouts:
        buf = _tcp_listeners(family)
        if buf is None:
            continue
        count = struct.unpack_from("<I", buf, 0)[0]
        row_size = struct.calcsize(row_fmt)
        for i in range(count):
            row = struct.unpack_from(row_fmt, buf, 4 + i * row_size)
            raw, pid = row[port_at], row[pid_at]
            # 포트는 네트워크 바이트 순서로 아래 두 바이트에 들어 있다
            port = ((raw & 0xFF) << 8) | ((raw >> 8) & 0xFF)
            found.setdefault(pid, set()).add(port)
    return {pid: sorted(ports) for pid, ports in found.items()}


def format_ports(ports: list) -> str:
    """가장 작은 포트 하나만 적고, 더 잡고 있으면 `+N` 으로 줄인다."""
    if not ports:
        return ""
    text = f":{ports[0]}"
    if len(ports) > 1:
        text += f"+{len(ports) - 1}"
    return text


EMPTY_MEMORY = {
    "total": 0, "used": 0, "load": 0, "cache": 0,
    "commit": 0, "commit_limit": 0, "page_size": 4096,
    "processes": 0, "threads": 0,
}


def read_memory() -> dict:
    """작업 관리자 '성능' 탭과 같은 기준으로 읽는다. 사용 중 = 전체 - 사용 가능."""
    info = dict(EMPTY_MEMORY)

    status = MEMORYSTATUSEX()
    status.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
    if kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
        info["total"] = status.ullTotalPhys
        info["used"] = status.ullTotalPhys - status.ullAvailPhys
        info["load"] = status.dwMemoryLoad

    perf = PERFORMANCE_INFORMATION()
    perf.cb = ctypes.sizeof(PERFORMANCE_INFORMATION)
    if kernel32.K32GetPerformanceInfo(ctypes.byref(perf), perf.cb):
        page = perf.PageSize or 4096
        info.update(
            {
                "page_size": page,
                "cache": perf.SystemCache * page,
                "commit": perf.CommitTotal * page,
                "commit_limit": perf.CommitLimit * page,
                "processes": perf.ProcessCount,
                "threads": perf.ThreadCount,
            }
        )
    return info


def read_pagefile(page_size: int) -> tuple:
    """(페이지 파일 사용 바이트, 전체 바이트). 맥의 스왑에 해당한다. 없으면 (0, 0)."""
    buf, _ = query_system(SYSTEM_PAGEFILE_INFO, 4096)
    if buf is None:
        return (0, 0)
    used = total = 0
    offset = 0
    while True:
        info = SYSTEM_PAGEFILE_INFORMATION.from_buffer(buf, offset)
        total += info.TotalSize
        used += info.TotalInUse
        if not info.NextEntryOffset:
            break
        offset += info.NextEntryOffset
    return (used * page_size, total * page_size)


def memory_pressure(mem: dict) -> tuple:
    """(표시글, 색, 덧붙일 말). 윈도우에는 맥 같은 압박 수준 값이 없어서 직접 판단한다.

    물리 메모리가 거의 찼거나, 커밋이 한계에 닿아가면 경고한다. 커밋이 한계에
    닿으면 페이지 파일이 늘어나지 못하는 한 새 프로그램이 메모리를 못 받는다.
    덧붙일 말은 경고일 때만 있다. 평소에 늘 떠 있으면 눈이 무뎌져 정작 필요할 때 안 읽힌다
    """
    commit_frac = mem["commit"] / mem["commit_limit"] if mem["commit_limit"] else 0.0
    if mem["load"] >= 95 or commit_frac >= 0.95:
        return ("위험", RED, "메모리가 바닥났다. 프로그램을 닫아야 한다")
    if mem["load"] >= 85 or commit_frac >= 0.85:
        return ("주의", YELLOW, "메모리가 빠듯하다. 안 쓰는 프로그램을 닫아 두면 좋다")
    return ("여유", GREEN, "")


# ── 프로세스 끝내기 ─────────────────────────────────────────────
def top_windows(pid: int) -> list:
    """그 프로세스가 띄운, 화면에 보이는 최상위 창들. 대화상자처럼 딸린 창은 뺀다."""
    found = []

    def visit(hwnd, _):
        owner = wintypes.DWORD()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(owner))
        if (
            owner.value == pid
            and user32.IsWindowVisible(hwnd)
            and not user32.GetWindow(hwnd, GW_OWNER)
        ):
            found.append(hwnd)
        return True

    user32.EnumWindows(WNDENUMPROC(visit), 0)
    return found


def close_windows(pid: int) -> int:
    """창에 닫기 요청(WM_CLOSE)을 보낸다. 창의 X 를 누른 것과 같다. 보낸 창 수를 돌려준다.

    윈도우에는 SIGTERM 같은 '정리하고 끝내라' 신호가 없다. os.kill 은 무슨 신호를
    주든 곧바로 강제 종료한다. 그래서 정상 종료는 창을 닫게 하는 것뿐이다.
    """
    sent = 0
    denied = False
    for hwnd in top_windows(pid):
        if user32.PostMessageW(hwnd, WM_CLOSE, 0, 0):
            sent += 1
        elif ctypes.get_last_error() == ERROR_ACCESS_DENIED:
            denied = True  # 관리자 권한으로 뜬 창에는 일반 권한으로 말을 못 건다
    if not sent and denied:
        raise PermissionError
    return sent


def terminate(pid: int) -> None:
    """강제 종료. 저장 안 한 작업은 그대로 날아간다."""
    handle = kernel32.OpenProcess(PROCESS_TERMINATE, False, pid)
    if not handle:
        err = ctypes.get_last_error()
        if err == ERROR_INVALID_PARAMETER:
            raise ProcessLookupError
        if err == ERROR_ACCESS_DENIED:
            raise PermissionError
        raise ctypes.WinError(err)
    try:
        if not kernel32.TerminateProcess(handle, 1):
            err = ctypes.get_last_error()
            if err == ERROR_ACCESS_DENIED:
                raise PermissionError
            raise ctypes.WinError(err)
    finally:
        kernel32.CloseHandle(handle)


# ── 표시 도우미 ─────────────────────────────────────────────────
def human_bytes(n: float) -> str:
    if n >= 1024**3:
        return f"{n / 1024**3:.1f}GB"
    if n >= 1024**2:
        return f"{n / 1024**2:.0f}MB"
    if n >= 1024:
        return f"{n / 1024:.0f}KB"
    return f"{int(n)}B"


def level_color(frac: float) -> str:
    if frac >= 0.85:
        return RED
    if frac >= 0.60:
        return YELLOW
    return GREEN


def proc_cpu_color(pct: float) -> str:
    """프로세스 CPU% 색. 값은 작업 관리자처럼 기기 전체 대비라서 기준을 따로 둔다."""
    if pct < 1:
        return GRAY
    if pct >= 50:
        return RED
    if pct * NCPU >= 90:  # 코어 하나를 거의 다 쓰고 있다. 무한 루프가 흔히 이렇다
        return YELLOW
    return GREEN


def draw_bar(frac: float, width: int, color: str = "") -> str:
    frac = max(0.0, min(1.0, frac))
    color = color or level_color(frac)
    filled = frac * width
    full = int(filled)
    body = "█" * full
    if full < width and not USE_ASCII:
        eighths = int((filled - full) * 8)
        if eighths > 0:
            body += BLOCKS[eighths - 1]
    empty = width - len(body)
    return f"{color}{body}{RESET}{DIM}{'·' * empty}{RESET}"


def draw_spark(values, width: int) -> str:
    """최근 CPU% 를 ▁▂▃▅▇ 한 줄로. 눈금은 0~100% 고정이다.

    가장 높은 값에 맞춰 늘리면 1~2% 흔들림도 산처럼 보여서 겁만 준다.
    """
    out = []
    for v in list(values)[-width:]:
        level = min(len(SPARKS) - 1, int(v / 100.0 * len(SPARKS)))
        out.append(f"{level_color(v / 100.0)}{SPARKS[level]}")
    return "".join(out) + RESET


def proc_mem_color(private: int, total: int) -> str:
    """프로세스 메모리 칸 색. 다 초록이면 정작 많이 먹는 게 안 보여서 작은 건 가라앉힌다."""
    if private < 100 * 1024**2:
        return GRAY
    color = level_color(private / total * 4 if total else 0.0)  # 한 프로세스가 25% 먹으면 빨강
    if color == GREEN and private < 1024**3:
        return ""  # 1GB 밑은 기본 글자색. 초록은 눈여겨볼 만큼 큰 것에만 쓴다
    return color


def dim_ext(cell: str) -> str:
    """이름 칸 끝의 .exe 를 흐리게. 거의 모든 줄에 붙어 있어 이름을 가린다."""
    name = cell.rstrip(" ")
    if not name.lower().endswith(".exe"):
        return cell
    return f"{name[:-4]}{GRAY}{name[-4:]}{RESET}{cell[len(name):]}"


def fit_extras(head_w: int, extras: list, cols: int) -> tuple:
    """요약 줄 뒤에 붙는 회색 정보를 창 폭에 맞춘다. (그릴 글자, 쓴 폭) 을 돌려준다.

    extras 는 (글자, 색, 남길 순위). 넘치면 순위 낮은 것부터 하나씩 뺀다. 한꺼번에
    접지 않는 건, 들어가는 한 가장 많이 보여주려는 것이다. 순위가 None 이면
    경고라서 빼지 않고, 대신 남은 폭만큼 줄여 끝에 … 를 단다.
    """
    items = list(extras)
    while head_w + sum(2 + dwidth(e[0]) for e in items) > cols:
        droppable = [i for i, e in enumerate(items) if e[2] is not None]
        if not droppable:
            break
        items.pop(min(droppable, key=lambda i: items[i][2]))
    out, used = [], head_w
    for text, color, _ in items:
        room = cols - used - 2
        if room < 4:
            break
        text = dtrunc(text, room)
        out.append(f"  {color}{text}{RESET}")
        used += 2 + dwidth(text)
    return "".join(out), used


# ── 화면 구성 ───────────────────────────────────────────────────
class Monitor:
    def __init__(self, interval: float, sort_key: str):
        self.interval = interval
        self.sort_key = sort_key  # "cpu" 또는 "mem"
        self.prev = {}  # {pid: (생성 시각, 누적 CPU 초)}
        self.prev_t = 0.0
        self.prev_times = None
        self.rows = []
        self.total_cpu = 0.0
        self.cpu_hist = collections.deque(maxlen=SPARK_LEN)  # 최근 전체 CPU%. 추이 그래프용
        self.ready = False
        # 수집 결과는 여기 담아둔다. 키를 눌러 다시 그릴 때 또 읽지 않으려는 것
        self.mem = dict(EMPTY_MEMORY)
        self.pagefile = (0, 0)
        self.compressed = 0
        self.interval_changed_at = 0.0  # 주기를 바꾼 직후 잠깐 강조하려고 기록
        self.latest_version = ""  # 새 버전 확인 결과. 별도 흐름에서 채운다
        # 프로세스 고르기와 종료 관련
        self.selected_pid = None  # 줄 번호가 아니라 PID 로 기억한다. 순위가 바뀌어도 따라가게
        self.scroll = 0
        self.visible_rows = 1
        self.ports = {}  # {PID: [포트, ...]}
        self.pending_kill = None  # 종료 확인을 기다리는 (PID, 이름, 생성 시각)
        self.status = ("", "", 0.0)  # (문구, 색, 띄운 시각)
        self.needs_refresh = False

    def start_version_check(self):
        """새 버전 확인을 뒷전으로 돌린다. 화면이 뜨는 걸 막지 않게 하려는 것."""
        cached = read_version_cache()
        if cached:
            self.latest_version = cached
            return

        def worker():
            found = fetch_latest_version(timeout=8)
            if found:
                self.latest_version = found
                write_version_cache(found)

        threading.Thread(target=worker, daemon=True).start()

    @property
    def update_ready(self) -> bool:
        return bool(self.latest_version) and parse_version(
            self.latest_version
        ) > parse_version(VERSION)

    def tick(self):
        now = time.monotonic()
        procs = sample_processes()
        self.ports = sample_ports()  # API 로 바로 읽어서 수 밀리초면 끝난다. 따로 돌릴 필요 없다
        self.mem = read_memory()
        self.pagefile = read_pagefile(self.mem["page_size"])

        # 전체 CPU 는 시스템 누적 시간으로 잰다. 프로세스를 더하는 방식은 인터럽트 처리
        # 시간을 놓치고, 재는 사이 끝난 프로세스 몫도 빠진다
        times = system_times()
        if times and self.prev_times:
            idle = times[0] - self.prev_times[0]
            busy_all = (times[1] - self.prev_times[1]) + (times[2] - self.prev_times[2])
            if busy_all > 0:
                self.total_cpu = max(0.0, min(100.0, (busy_all - idle) / busy_all * 100.0))
                self.cpu_hist.append(self.total_cpu)
                self.ready = True
        self.prev_times = times

        rows = []
        compressed = 0
        elapsed = now - self.prev_t if self.prev_t else 0.0
        for pid, (born, cpu_s, private, ws, name) in procs.items():
            pct = 0.0
            before = self.prev.get(pid)
            # 윈도우는 PID 를 금방 다시 쓴다. 생성 시각까지 같아야 같은 프로세스다
            if elapsed > 0 and before and before[0] == born:
                delta = cpu_s - before[1]
                if delta > 0:
                    # 작업 관리자처럼 기기 전체 대비 % 로 적는다. 8코어면 코어 하나 = 12.5%
                    pct = min(100.0, delta / (elapsed * NCPU) * 100.0)
            if name == "Memory Compression":
                compressed = ws  # 압축해 담아둔 메모리는 이 프로세스의 작업 집합으로 잡힌다
            rows.append((pid, pct, private, name))

        self.compressed = compressed
        self.rows = rows
        self.prev = {pid: (p[0], p[1]) for pid, p in procs.items()}
        self.prev_t = now

    def sorted_rows(self):
        idx = 1 if self.sort_key == "cpu" else 2
        return sorted(self.rows, key=lambda r: r[idx], reverse=True)

    def set_status(self, text: str, color: str = GRAY):
        self.status = (text, color, time.monotonic())

    def move_selection(self, step: int):
        rows = self.sorted_rows()
        if not rows:
            return
        pids = [r[0] for r in rows]
        if self.selected_pid in pids:
            index = pids.index(self.selected_pid) + step
        else:
            index = 0 if step >= 0 else len(pids) - 1
        index = max(0, min(len(pids) - 1, index))
        self.selected_pid = pids[index]

        # 고른 줄이 화면 밖으로 나가면 따라 굴린다
        if index < self.scroll:
            self.scroll = index
        elif index >= self.scroll + self.visible_rows:
            self.scroll = index - self.visible_rows + 1

    def request_kill(self):
        """확인 단계로 넘긴다. 여기서 막을 건 미리 막는다."""
        rows = self.sorted_rows()
        target = next((r for r in rows if r[0] == self.selected_pid), None)
        if target is None:
            self.set_status("먼저 ↑ ↓ 로 프로세스를 고르라", YELLOW)
            return
        pid, _, _, name = target
        if pid in PROTECTED_PIDS or name.lower() in PROTECTED_NAMES:
            self.set_status(f"{name} 은 윈도우가 돌아가는 데 필요하다. 종료 못 한다", RED)
            return
        if pid == os.getpid():
            self.set_status("wsc 자신이다. 끄려면 q 를 눌러라", YELLOW)
            return
        born = self.prev.get(pid, (None,))[0]
        self.pending_kill = (pid, name, born)

    def do_kill(self, force: bool):
        pid, name, born = self.pending_kill
        self.pending_kill = None
        # 확인을 기다리는 사이 그 프로세스가 끝나고 같은 PID 로 딴 게 떴을 수 있다.
        # 그걸 엉뚱하게 죽이지 않도록 방금 읽은 목록으로 다시 맞춰본다
        fresh = sample_processes().get(pid)
        if fresh is None or fresh[0] != born:
            self.set_status(f"PID {pid} {name} 은 이미 없다", GRAY)
            self.needs_refresh = True
            return
        try:
            if force:
                terminate(pid)
                how = "강제 종료함"
            else:
                sent = close_windows(pid)
                if not sent:
                    self.set_status(
                        f"PID {pid} {name} 은 닫을 창이 없다. 끝내려면 k 다음 f 로 강제 종료",
                        YELLOW,
                    )
                    return
                how = "창 닫기 요청 보냄"
        except ProcessLookupError:
            self.set_status(f"PID {pid} {name} 은 이미 없다", GRAY)
        except PermissionError:
            self.set_status(
                f"PID {pid} {name} 종료 권한이 없다. 관리자 권한 터미널에서 wsc 를 띄워야 한다",
                RED,
            )
        except OSError as exc:
            self.set_status(f"PID {pid} {name} 종료 실패 ({exc})", RED)
        else:
            self.set_status(f"PID {pid} {name} {how}", GREEN)
            self.needs_refresh = True

    def render(self, cols: int, lines: int) -> list:
        cols = max(52, cols)
        mem = self.mem
        page_used, page_total = self.pagefile
        pressure_text, pressure_color, pressure_note = memory_pressure(mem)

        bar_w = max(12, min(28, cols - 44))
        label_w = 7
        out = []

        # 제목 줄
        # 폭 계산은 색 코드를 뺀 순수 글자로만 한다. 오른쪽 정보가 먼저고, 남는 자리에 CPU 이름을 넣는다
        rate_note = ""
        if self.interval >= INTERVAL_MAX:
            rate_note = " (최대)"
        elif self.interval <= INTERVAL_MIN:
            rate_note = " (최소)"
        rate = f"{self.interval:.1f}초{rate_note}"
        # 방금 +/- 로 바꿨으면 잠깐 노랗게 띄워서 눈에 걸리게 한다
        just_changed = time.monotonic() - self.interval_changed_at < 1.5
        rate_color = f"{YELLOW}{BOLD}" if just_changed else BOLD
        clock = time.strftime("%H:%M:%S")
        admin = "관리자  " if IS_ADMIN else ""
        right = f"{admin}{clock}  갱신 {rate} "
        name = f" wsc {VERSION}  "
        brand_w = cols - dwidth(name) - dwidth(right) - 2
        brand = dtrunc(CPU_BRAND, brand_w) if brand_w >= 6 else ""
        pad = max(1, cols - dwidth(name) - dwidth(brand) - dwidth(right))
        admin_cell = f"{YELLOW}{BOLD}{admin}{RESET}{HEADER_BG}" if admin else ""
        out.append(
            f"{HEADER_BG}{LOGO_ON_HEADER} wsc {GRAY_ON_HEADER}{VERSION}  {RESET}{HEADER_BG}{brand}"
            f"{' ' * pad}{admin_cell}{BOLD}{clock}{RESET}{HEADER_BG}  "
            f"{GRAY_ON_HEADER}갱신 {rate_color}{rate} {RESET}"
        )
        out.append("")

        # 값 칸은 '쓰는 양 / 전체' 두 칸으로 나눠 폭을 고정한다. 앞 숫자끼리 오른쪽 끝이 맞고,
        # 뒤의 회색 정보도 한 세로줄에 선다. 자릿수가 바뀔 때마다 줄이 들썩이지도 않는다
        values = {
            "cpu": (f"{self.total_cpu:.1f}%" if self.ready else "측정 중", ""),
            "mem": (human_bytes(mem["used"]), human_bytes(mem["total"])),
            "commit": (human_bytes(mem["commit"]), human_bytes(mem["commit_limit"])),
            "page": (
                (human_bytes(page_used), human_bytes(page_total)) if page_total else ("꺼 둠", "")
            ),
        }
        left_w = max(7, *(dwidth(v[0]) for v in values.values()))
        right_w = max(7, *(dwidth(v[1]) for v in values.values()))
        head_w = 1 + label_w + bar_w + 2 + left_w + 3 + right_w

        def summary(label, frac, key, extras, color="", reserve=0):
            used_text, total_text = values[key]
            total_cell = f" / {dpad(total_text, right_w)}" if total_text else " " * (3 + right_w)
            tail, used = fit_extras(head_w + reserve, extras, cols)
            line = (
                f" {dpad(label, label_w)}{draw_bar(frac, bar_w, color)}  "
                f"{BOLD}{rpad(used_text, left_w)}{total_cell}{RESET}{tail}"
            )
            return line, used - reserve

        # CPU — 윈도우에는 부하 평균이 없어서 그 자리에 프로세스·스레드 수를 둔다.
        # 끝에는 최근 추이를 붙인다. 방금 튄 건지 계속 높은 건지가 한눈에 갈린다.
        # 추이 자리를 먼저 떼어 두고, 남는 폭에 회색 정보를 순위대로 채운다
        spark_room = 2 + 12 if len(self.cpu_hist) >= 2 else 0
        line, used = summary(
            "CPU", self.total_cpu / 100.0, "cpu",
            [
                (f"{NCPU}코어", GRAY, 3),
                (f"프로세스 {mem['processes']}", GRAY, 2),
                (f"스레드 {mem['threads']}", GRAY, 1),
            ],
            reserve=spark_room,
        )
        spark_w = min(SPARK_LEN, cols - used - 2)
        if spark_room and spark_w >= 8:
            line += f"  {draw_spark(self.cpu_hist, spark_w)}"
        out.append(line)

        # 메모리. 좁으면 캐시부터 뺀다. 압축이 쌓이는 건 부족 신호라 더 오래 남긴다
        mem_frac = mem["used"] / mem["total"] if mem["total"] else 0.0
        out.append(summary(
            "메모리", mem_frac, "mem",
            [
                (f"압축 {human_bytes(self.compressed)}", GRAY, 2),
                (f"캐시 {human_bytes(mem['cache'])}", GRAY, 1),
            ],
        )[0])

        # 커밋 — 프로그램들이 '쓰겠다'고 받아간 메모리 총량. 한계에 닿으면 새 할당이 실패한다
        commit_frac = mem["commit"] / mem["commit_limit"] if mem["commit_limit"] else 0.0
        commit_note = []
        if commit_frac >= 0.90:
            commit_note = [("한계 가까움 — 새 프로그램이 안 열릴 수 있다", f"{RED}{BOLD}", None)]
        elif commit_frac >= 0.80:
            commit_note = [("여유 적음", YELLOW, None)]
        out.append(summary("커밋", commit_frac, "commit", commit_note)[0])

        # 페이지 파일 — 맥의 스왑. 비율보다 절대량이 중요해서 색도 양으로 정한다
        page_note = []
        page_color = GREEN
        if page_used >= 3 * 1024**3:
            page_color = RED
            page_note = [("디스크로 많이 밀려남 — 렉의 주범", f"{RED}{BOLD}", None)]
        elif page_used >= 1024**3:
            page_color = YELLOW
            page_note = [("메모리 부족 조짐", YELLOW, None)]
        page_frac = page_used / page_total if page_total else 0.0
        out.append(summary("페이지", page_frac, "page", page_note, page_color)[0])

        # 압박 — 색 배지 하나로. 설명은 경고일 때만 붙인다
        badge = f"{PRESSURE_BADGE[pressure_text]}{BOLD} {pressure_text} {RESET}"
        line = f" {dpad('압박', label_w)}{badge}"
        if pressure_note:
            room = cols - (1 + label_w + dwidth(pressure_text) + 2 + 2)
            line += f"  {pressure_color}{dtrunc(pressure_note, room)}{RESET}"
        out.append(line)
        out.append("")

        # 프로세스 표
        # 포트 칸은 자리가 있을 때만 낸다. 좁은 창에서는 이름이 먼저다
        port_w = 9 if cols >= 76 else 0
        # 이름 칸이 창 끝까지 간다. 제목 줄·조작 줄과 오른쪽 끝이 맞아야 표가 반듯해 보인다
        name_w = max(14, cols - 29 - (port_w + 2 if port_w else 0))
        # 색 코드는 폭 계산 뒤에 감싼다. 안 그러면 이스케이프 문자까지 폭으로 세서 표가 어긋난다
        # 정렬 기준 칸에는 ▼ 를 붙인다. 굵은 글씨만으로는 어느 쪽인지 잘 안 보인다
        cpu_hdr = rpad("CPU%▼" if self.sort_key == "cpu" else "CPU%", 7)
        mem_hdr = rpad("메모리▼" if self.sort_key == "mem" else "메모리", 8)
        if self.sort_key == "cpu":
            cpu_hdr = f"{BOLD}{cpu_hdr}{RESET}{HEADER_BG}"
        else:
            mem_hdr = f"{BOLD}{mem_hdr}{RESET}{HEADER_BG}"
        port_hdr = f"{dpad('포트', port_w)}  " if port_w else ""
        out.append(
            f"{HEADER_BG} {rpad('PID', 7)}  {cpu_hdr}  {mem_hdr}  "
            f"{port_hdr}{dpad('이름', name_w)}{RESET}"
        )

        used_lines = len(out) + 2  # 표 아래 상태 줄과 도움말 줄 확보
        limit = max(3, lines - used_lines)
        self.visible_rows = limit

        rows = self.sorted_rows()
        # 고른 줄이 목록 밖으로 나가지 않게 굴림 위치를 다듬는다
        self.scroll = max(0, min(self.scroll, max(0, len(rows) - limit)))
        window = rows[self.scroll : self.scroll + limit]

        # 몇 번째를 보고 있는지 알리는 꼬리표. 마지막 줄에 그냥 붙이면 줄이 창 폭을
        # 넘어 다음 줄로 접히고, 그만큼 화면이 밀려 올라간다. 그래서 그 줄만
        # 이름 칸을 미리 좁혀 자리를 만들어 둔다
        count_note = ""
        if len(rows) > limit:
            shown = f"{self.scroll + 1}–{min(self.scroll + limit, len(rows))}"
            count_note = f" {shown}/{len(rows)}"

        for idx, (pid, pct, private, name) in enumerate(window):
            last_row = idx == len(window) - 1
            col_w = max(6, name_w - dwidth(count_note)) if last_row else name_w
            chosen = pid == self.selected_pid
            port_text = format_ports(self.ports.get(pid, [])) if port_w else ""
            name_cell = dpad(name, col_w)
            if chosen:
                # 고른 줄은 색을 다 빼고 흰 글씨 하나로. 파란 바탕 위 색 글자는 안 읽힌다
                port_cell = f"{dpad(port_text, port_w)}  " if port_w else ""
                body = (
                    f"›{pid:>7}  {pct:>7.1f}  {human_bytes(private):>8}  "
                    f"{port_cell}{name_cell}"
                )
                line = f"{SELECT_BG}{BOLD}{body}{RESET}"
            else:
                port_cell = ""
                if port_w:
                    port_color = CYAN if port_text else DIM
                    port_cell = f"{port_color}{dpad(port_text, port_w)}{RESET}  "
                mem_color = proc_mem_color(private, mem["total"])
                line = (
                    f" {pid:>7}  {proc_cpu_color(pct)}{pct:>7.1f}{RESET}  "
                    f"{mem_color}{human_bytes(private):>8}{RESET}  "
                    f"{port_cell}{dim_ext(name_cell)}"
                )
            if last_row and count_note:
                line += f"{GRAY}{count_note}{RESET}"
            out.append(line)

        # 알림 줄. 없으면 빈 줄로 남겨 아래 도움말 위치가 흔들리지 않게 한다
        text, color, shown_at = self.status
        if text and time.monotonic() - shown_at < 5.0:
            out.append(f"{color} {dtrunc(text, cols - 2)}{RESET}")
        elif self.update_ready:
            # 알릴 말이 없을 때만. 조작 줄에 끼워 넣으면 '누를 것'과 섞여 헷갈린다
            note = f"새 버전 {self.latest_version} 이 있다 — 끄고 wsc --update"
            out.append(f"{CYAN}{BOLD} {dtrunc(note, cols - 2)}{RESET}")
        else:
            out.append("")

        if self.pending_kill:
            pid, name, _ = self.pending_kill
            keys, keys_w = "", 0
            for key, label in (("y", "창 닫기"), ("f", "강제"), ("n", "취소")):
                keys += f"{KEY_BG}{BOLD} {key} {RESET}{DANGER_BG}{BOLD} {label}  "
                keys_w += dwidth(key) + dwidth(label) + 5
            question = f" {dtrunc(name, max(10, cols - keys_w - 22))} (PID {pid}) 를 종료한다"
            out.append(
                f"{DANGER_BG}{BOLD}{dpad(question, max(1, cols - keys_w))}{keys}{RESET}"
            )
            return out

        # 조작 줄. 누르는 키는 자판 모양으로, 설명글은 그 옆에 차분하게 둔다.
        # 갱신 주기·정렬 같은 '지금 상태'는 제목 줄과 표 머리에 이미 있으니
        # 여기서는 빼서, 이 줄은 오로지 '누를 것'만 남게 한다
        # (키, 긴 설명, 짧은 설명, 설명 없이도 뜻이 통하는가, 지금 켜져 있는가)
        keys = [
            ("↑↓", "고르기", "선택", True, False),
            ("k", "종료시키기", "종료", False, False),
            ("c", "CPU순", "CPU", False, self.sort_key == "cpu"),
            ("m", "메모리순", "메모리", False, self.sort_key == "mem"),
            ("+/-", "갱신 간격", "간격", False, False),
            ("q", "나가기", "끝", True, False),
        ]
        # 좁은 창이라고 설명글을 한꺼번에 접으면 k·c·m 이 무슨 키인지 알 길이 없다.
        # 긴 설명 → 짧은 설명 → 간격 줄이기 → 뻔한 키(↑↓, q)의 설명 빼기 순으로
        # 조금씩 줄여서, 들어가는 한 가장 자세한 모양을 쓴다. 키는 하나도 빠뜨리지 않는다
        tiers = [
            (lambda k: k[1], 2),
            (lambda k: k[2], 2),
            (lambda k: k[2], 1),
            (lambda k: "" if k[3] else k[2], 1),
            (lambda k: "", 1),
        ]

        def width_of(label_of, gap):
            w = 1
            for k in keys:
                label = label_of(k)
                w += dwidth(k[0]) + 2 + gap
                if label:
                    w += 1 + dwidth(label)
                elif k[4]:
                    w += 1  # 설명이 빠져도 켜진 정렬 기준은 · 로 남긴다
            return w

        label_of, gap = next(
            ((f, g) for f, g in tiers if width_of(f, g) <= cols), tiers[-1]
        )

        bar = [FOOTER_BG, " "]
        used = 1
        for k in keys:
            key, active = k[0], k[4]
            label = label_of(k)
            bar.append(f"{KEY_BG}{BOLD} {key} {RESET}{FOOTER_BG}")
            used += dwidth(key) + 2
            if label:
                bar.append(f" {FOOTER_ON if active else FOOTER_TEXT}{label}{FOOTER_TEXT}")
                used += 1 + dwidth(label)
            elif active:
                bar.append(f"{FOOTER_ON}·{FOOTER_TEXT}")
                used += 1
            bar.append(" " * gap)
            used += gap
        bar.append(" " * max(0, cols - used))
        bar.append(RESET)
        out.append("".join(bar))
        return out

    def handle_key(self, key: str) -> bool:
        """계속 실행하면 True, 종료하면 False."""
        # 종료 확인 중에는 다른 키를 다 막는다. 실수로 딴 걸 눌러 진행되면 안 된다
        if self.pending_kill:
            if key in ("y", "Y"):
                self.do_kill(force=False)
            elif key in ("f", "F"):
                self.do_kill(force=True)
            else:
                pid, name, _ = self.pending_kill
                self.pending_kill = None
                self.set_status(f"PID {pid} {name} 종료를 취소했다", GRAY)
            return True

        if key in ("q", "Q", "\x03", "\x04"):
            return False
        if key == "UP":
            self.move_selection(-1)
        elif key == "DOWN":
            self.move_selection(1)
        elif key == "PGUP":
            self.move_selection(-self.visible_rows)
        elif key == "PGDN":
            self.move_selection(self.visible_rows)
        elif key == "HOME":
            self.move_selection(-len(self.rows))
        elif key == "END":
            self.move_selection(len(self.rows))
        elif key in ("k", "K"):
            self.request_kill()
        elif key == "ESC":
            self.selected_pid = None
        elif key in ("c", "C"):
            self.sort_key = "cpu"
        elif key in ("m", "M"):
            self.sort_key = "mem"
        elif key in ("+", "="):
            self.interval = min(INTERVAL_MAX, round(self.interval + 0.5, 1))
            self.interval_changed_at = time.monotonic()
        elif key in ("-", "_"):
            self.interval = max(INTERVAL_MIN, round(self.interval - 0.5, 1))
            self.interval_changed_at = time.monotonic()
        return True


# ── 키보드와 콘솔 ───────────────────────────────────────────────
# 방향키 같은 특수 키는 \xe0(또는 \x00) 다음에 글자 하나가 한 번 더 온다
SPECIAL_KEYS = {
    "H": "UP", "P": "DOWN", "K": "LEFT", "M": "RIGHT",
    "I": "PGUP", "Q": "PGDN", "G": "HOME", "O": "END",
}


def key_waiting(timeout: float) -> bool:
    """누른 키가 있는지 본다. 없으면 timeout 동안 짧게 끊어 가며 기다린다.

    윈도우의 select 는 소켓만 기다릴 수 있어서 콘솔 입력에는 못 쓴다.
    30ms 마다 살피는 정도면 CPU 는 거의 안 들고, 손으로 누르는 키에는 충분히 빠르다.
    """
    end = time.monotonic() + timeout
    while True:
        if msvcrt.kbhit():
            return True
        left = end - time.monotonic()
        if left <= 0:
            return False
        time.sleep(min(KEY_POLL, left))


def read_key() -> str:
    ch = msvcrt.getwch()
    if ch in ("\x00", "\xe0"):
        return SPECIAL_KEYS.get(msvcrt.getwch(), "")
    if ch == "\x1b":
        return "ESC"
    return ch


def enable_vt():
    """콘솔이 ANSI 제어 문자를 알아듣게 켠다. 원래 모드를 돌려준다. 못 켜면 None.

    Windows Terminal 은 처음부터 켜져 있지만, 옛 콘솔 창(conhost)은 켜 줘야
    색 코드가 글자 그대로 찍히지 않는다.
    """
    handle = kernel32.GetStdHandle(STD_OUTPUT_HANDLE)
    mode = wintypes.DWORD()
    if not kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
        return None
    if not mode.value & ENABLE_VIRTUAL_TERMINAL_PROCESSING:
        if not kernel32.SetConsoleMode(handle, mode.value | ENABLE_VIRTUAL_TERMINAL_PROCESSING):
            return None
    return mode.value


def restore_console_mode(mode):
    if mode is not None:
        kernel32.SetConsoleMode(kernel32.GetStdHandle(STD_OUTPUT_HANDLE), mode)


def wants_ascii() -> bool:
    """옛 콘솔을 한중일 코드 페이지로 쓰는 중이면 영문 기호로 그린다.

    Windows Terminal(WT_SESSION)이나 VS Code 같은 터미널(TERM_PROGRAM)은
    폭이 애매한 글자를 한 칸으로 그려서 괜찮다.
    """
    if os.environ.get("WT_SESSION") or os.environ.get("TERM_PROGRAM"):
        return False
    return kernel32.GetConsoleOutputCP() in (932, 936, 949, 950)


def term_size():
    """창 크기. 터미널이 떨어져 나가도 죽지 않게 기본값을 둔다."""
    try:
        size = os.get_terminal_size()
        if size.columns and size.lines:
            return size
    except OSError:
        pass
    return os.terminal_size((100, 30))


ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")


def clip(s: str, width: int) -> str:
    """색 코드는 폭으로 세지 않고 남긴 채, 표시 폭 기준으로 자른다.

    한 줄이라도 창 폭을 넘으면 터미널이 다음 줄로 접어 화면을 밀어 올린다.
    색 코드를 남기는 이유는 끝에 붙은 RESET 이 잘려나가면 그 뒤 화면 전체가
    같은 색으로 물들기 때문이다.
    """
    out, used, i = [], 0, 0
    while i < len(s):
        m = ANSI_RE.match(s, i)
        if m:
            out.append(m.group())
            i = m.end()
            continue
        ch = s[i]
        i += 1
        w = 0 if unicodedata.combining(ch) else (
            2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
        )
        if used + w > width:
            continue
        out.append(ch)
        used += w
    return "".join(out)


def draw(lines_out, cols: int, rows: int):
    """깜빡임 없이 화면 갱신 — 지우고 그리지 않고 덮어쓴다.

    마지막 줄 뒤에는 줄바꿈을 찍지 않는다. 화면 맨 아래 칸에서 줄바꿈을 보내면
    터미널이 화면을 한 줄 밀어 올리고, 밀려난 제목줄이 스크롤 기록에 쌓인다.
    줄 수도 화면 높이로 자른다 — 창이 아주 낮으면 render 가 더 만들 수 있다.
    """
    lines_out = [clip(line, cols) for line in lines_out[: max(1, rows)]]
    frame = "".join(
        [CURSOR_HOME, (CLEAR_LINE + "\n").join(lines_out), CLEAR_LINE, CLEAR_BELOW]
    )
    if USE_ASCII:
        frame = frame.translate(ASCII_MAP)
    sys.stdout.write(frame)
    sys.stdout.flush()


def run_interactive(monitor: Monitor) -> int:
    saved_mode = enable_vt()
    if saved_mode is None:
        print(
            "이 콘솔은 화면 제어 문자를 못 알아듣는다. "
            "Windows 10 이상에서 Windows Terminal 로 실행해라.",
            file=sys.stderr,
        )
        return 1

    sys.stdout.write(ALT_SCREEN_ON + CURSOR_HIDE)
    sys.stdout.flush()

    def on_break(*_):
        raise KeyboardInterrupt

    # Ctrl-Break 는 Ctrl-C 와 따로 온다. 같은 길로 빠져나가 화면을 되돌려 놓게 한다
    signal.signal(signal.SIGBREAK, on_break)

    try:
        monitor.tick()  # 차분 계산의 기준점
        size = term_size()
        draw(monitor.render(size.columns, size.lines), size.columns, size.lines)

        deadline = time.monotonic() + monitor.interval
        while True:
            # 키 검사를 먼저, 조건 없이 한다. 한 장 그리는 시간이 갱신 주기보다 길어지면
            # 갱신 분기에만 걸려서 키가 영영 안 읽히기 때문이다
            remaining = max(0.0, deadline - time.monotonic())
            if key_waiting(remaining):
                quit_now = False
                while msvcrt.kbhit():  # 밀린 키는 한 번에 다 처리한다
                    if not monitor.handle_key(read_key()):
                        quit_now = True
                        break
                if quit_now:
                    break
                # 주기를 바꿨으면 다음 갱신 시점도 다시 잡는다
                deadline = min(deadline, time.monotonic() + monitor.interval)

            if monitor.needs_refresh:
                # 프로세스를 종료시킨 직후. 목록에서 바로 빠지게 즉시 다시 읽는다
                monitor.needs_refresh = False
                monitor.tick()
                deadline = time.monotonic() + monitor.interval

            if time.monotonic() >= deadline:
                monitor.tick()
                deadline = time.monotonic() + monitor.interval

            size = term_size()
            draw(monitor.render(size.columns, size.lines), size.columns, size.lines)
    except KeyboardInterrupt:
        pass
    finally:
        sys.stdout.write(CURSOR_SHOW + ALT_SCREEN_OFF)
        sys.stdout.flush()
        restore_console_mode(saved_mode)
    return 0


def run_once(monitor: Monitor) -> int:
    """파이프나 파일로 넘길 때 쓰는 1회 출력 모드 (색·제어문자 없음).

    인코딩은 콘솔 코드 페이지를 따른다. PowerShell 은 프로그램 출력을 그 코드
    페이지로 읽어 들이므로, UTF-8 로 내보내면 `wsc > a.txt` 에서 한글이 깨진다.
    막대 글자는 코드 페이지에 없을 수 있어 영문 기호로 바꾸고, 그래도 없는 글자는 ? 로 둔다.
    """
    cp = kernel32.GetConsoleOutputCP()
    try:
        sys.stdout.reconfigure(
            encoding="utf-8" if cp in (0, 65001) else f"cp{cp}", errors="replace"
        )
    except (LookupError, AttributeError, ValueError):
        pass

    monitor.tick()
    time.sleep(monitor.interval)
    monitor.tick()
    lines = monitor.render(100, 30)
    strip = re.compile(r"\x1b\[[0-9;]*m")
    for line in lines:
        line = strip.sub("", line)
        print((line.translate(ASCII_MAP) if USE_ASCII else line).rstrip())
    return 0


CACHE_FILE = os.path.join(
    os.environ.get("LOCALAPPDATA") or os.path.expanduser("~"), "wsc", "version"
)
CACHE_MAX_AGE = 86400  # 하루에 한 번만 물어본다


def open_raw(timeout: int):
    """깃허브 raw 파일을 연다.

    raw 서버는 응답에 max-age=300 을 달아 최대 5분간 예전 내용을 돌려준다.
    익명 요청에는 캐시 무시 헤더도 질의 문자열도 안 먹혀서, 방금 올린 버전은
    5분쯤 뒤에야 보인다. 아래 헤더는 중간 프록시용이고 raw 서버는 무시한다.
    """
    request = urllib.request.Request(
        RAW_URL,
        headers={
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
            "User-Agent": f"wsc/{VERSION}",
        },
    )
    return urllib.request.urlopen(request, timeout=timeout)


def fetch_latest_version(timeout: int = 20) -> str:
    """깃허브에 올라간 파일에서 버전 문자열만 뽑는다. 실패하면 빈 문자열."""
    try:
        with open_raw(timeout) as resp:
            head = resp.read(4096).decode("utf-8", "replace")
    except Exception:
        return ""
    found = re.search(r'^VERSION = "([^"]+)"', head, re.M)
    return found.group(1) if found else ""


def read_version_cache() -> str:
    """하루 안에 확인한 결과가 있으면 그걸 쓴다. 없으면 빈 문자열."""
    try:
        if time.time() - os.path.getmtime(CACHE_FILE) > CACHE_MAX_AGE:
            return ""
        with open(CACHE_FILE, encoding="utf-8") as fp:
            return fp.read().strip()
    except OSError:
        return ""


def write_version_cache(value: str) -> None:
    try:
        os.makedirs(os.path.dirname(CACHE_FILE), exist_ok=True)
        with open(CACHE_FILE, "w", encoding="utf-8") as fp:
            fp.write(value)
    except OSError:
        pass  # 저장 실패는 무시한다. 다음에 다시 물어보면 그만


def parse_version(raw: str) -> tuple:
    """'1.2.3' 을 비교 가능한 숫자 묶음으로. 못 읽으면 (0,) 을 준다."""
    try:
        return tuple(int(part) for part in raw.split("."))
    except ValueError:
        return (0,)


def self_update(check_only: bool = False) -> int:
    """깃허브의 최신 파일을 받아 자기 자신을 덮어쓴다."""
    target = os.path.realpath(os.path.abspath(__file__))
    print(f"설치 위치  {target}")
    print(f"현재 버전  {VERSION}")
    print(f"확인 주소  {RAW_URL}")

    try:
        with open_raw(20) as resp:
            payload = resp.read()
    except urllib.error.HTTPError as exc:
        print(f"\n실패: 서버가 {exc.code} 로 거절했다. 레포가 비공개거나 주소가 바뀌었다.")
        return 1
    except Exception as exc:
        print(f"\n실패: 내려받지 못했다 ({exc}). 인터넷 연결을 확인해라.")
        return 1

    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        print("\n실패: 받은 파일이 깨져 있다.")
        return 1

    found = re.search(r'^VERSION = "([^"]+)"', text, re.M)
    latest = found.group(1) if found else ""
    print(f"최신 버전  {latest or '표시 없음'}")

    with open(target, "rb") as fp:
        current = fp.read()

    # 깃이 줄 끝을 CRLF 로 바꿔 받았을 수 있다. 줄 끝만 다른 건 같은 파일로 본다
    if current.replace(b"\r\n", b"\n") == payload.replace(b"\r\n", b"\n"):
        print("\n이미 최신이다. 받을 것 없음.")
        return 0
    if not latest:
        print("\n받은 파일에 버전 표시가 없다. 안전하게 덮어쓰지 않는다.")
        print(f"직접 확인해라: {REPO_URL}")
        return 1
    if parse_version(latest) < parse_version(VERSION):
        print(f"\n서버 쪽이 더 낮다 ({latest} < {VERSION}). 덮어쓰지 않는다.")
        return 1
    if check_only:
        print(f"\n새 버전 {latest} 이 있다. 받으려면: wsc --update")
        return 0

    # 문법이 깨진 파일로 덮어쓰면 프로그램이 아예 안 열린다. 미리 검사한다
    try:
        compile(text, target, "exec")
    except SyntaxError as exc:
        print(f"\n실패: 받은 파일에 문법 오류가 있다 ({exc}). 덮어쓰지 않는다.")
        return 1

    folder = os.path.dirname(target)
    backup = target + ".bak"
    try:
        # 같은 폴더에 임시로 쓴 뒤 한 번에 바꿔치기한다. 도중에 끊겨도 원본이 안 깨진다
        handle, temp = tempfile.mkstemp(dir=folder, prefix=".wsc-update-")
        with os.fdopen(handle, "wb") as fp:
            fp.write(payload)
        with open(backup, "wb") as fp:
            fp.write(current)
        os.replace(temp, target)
    except PermissionError:
        print(f"\n실패: {target} 에 쓸 권한이 없다.")
        print("시작 메뉴에서 터미널을 '관리자 권한으로 실행'한 뒤 다시 해라.")
        return 1
    except OSError as exc:
        print(f"\n실패: 파일을 바꾸지 못했다 ({exc}).")
        return 1

    print(f"\n{VERSION} → {latest} 로 바꿨다.")
    print(f"이전 버전은 {backup} 에 남겨뒀다. 문제 없으면 지워도 된다.")
    return 0


def main():
    global USE_ASCII

    parser = argparse.ArgumentParser(
        prog="wsc",
        description="윈도우 CPU·메모리 사용량과 많이 먹는 프로세스를 터미널에 보여준다.",
    )
    parser.add_argument(
        "-i", "--interval", type=float, default=2.0, help="갱신 주기(초). 기본 2.0"
    )
    parser.add_argument(
        "-s",
        "--sort",
        choices=["cpu", "mem"],
        default="cpu",
        help="정렬 기준. 기본 cpu",
    )
    glyphs = parser.add_mutually_exclusive_group()
    glyphs.add_argument(
        "--ascii", action="store_true", help="막대·기호를 영문 기호로 그린다 (표가 어긋날 때)"
    )
    glyphs.add_argument(
        "--unicode", action="store_true", help="막대·기호를 늘 유니코드로 그린다"
    )
    parser.add_argument(
        "-u", "--update", action="store_true", help="깃허브에서 최신 버전으로 갱신"
    )
    parser.add_argument(
        "--check-update", action="store_true", help="갱신할 게 있는지 확인만 한다"
    )
    parser.add_argument(
        "-v", "--version", action="version", version=f"wsc {VERSION}  {REPO_URL}"
    )
    parser.add_argument(
        "--no-check", action="store_true", help="실행할 때 새 버전 확인을 건너뛴다"
    )
    args = parser.parse_args()

    if args.update or args.check_update:
        return self_update(check_only=args.check_update)

    interval = min(INTERVAL_MAX, max(INTERVAL_MIN, args.interval))
    monitor = Monitor(interval, args.sort)
    if not args.no_check:
        monitor.start_version_check()
    if sys.stdout.isatty() and sys.stdin.isatty():
        USE_ASCII = args.ascii or (not args.unicode and wants_ascii())
        return run_interactive(monitor)
    USE_ASCII = not args.unicode  # 파일·파이프는 코드 페이지에 없는 막대 글자가 ? 로 깨진다
    return run_once(monitor)


if __name__ == "__main__":
    sys.exit(main())
