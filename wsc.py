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
import math
import os
import random
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
    sys.exit("wsc 는 Windows 전용입니다. macOS 에서는 msc 를 쓰세요: https://github.com/seeminglyjs/msc")

import msvcrt  # noqa: E402  윈도우에만 있는 모듈이라 위의 검사 뒤에 불러온다
import winreg  # noqa: E402
from ctypes import wintypes  # noqa: E402

VERSION = "1.9.0"
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
# 한 장을 다 받을 때까지 화면에 안 그리게 하는 묶음 (동기화 출력). 애니메이션 중 반쯤 그린
# 화면이 비치는 걸 막는다. 모르는 터미널은 그냥 무시한다
SYNC_ON = f"{ESC}[?2026h"
SYNC_OFF = f"{ESC}[?2026l"
BEL = "\x07"
TASKBAR_CLEAR = f"{ESC}]9;4;0;0{BEL}"  # 작업 표시줄 아이콘의 진행 막대를 걷는다

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

SPARKS = "▁▂▃▄▅▆▇█"
SPARK_LEN = 20  # CPU 줄 끝의 추이로 보여줄 최근 갱신 횟수
CPU_HIST_MAX = 1000  # 추이 그래프용으로 기억할 CPU% 개수. 아주 넓은 창도 끝까지 채운다
# 추이 그래프는 점자 글자(⣿)로 그린다. 한 칸에 점이 가로 2 × 세로 4 라서 ▁▂▃ 보다
# 가로로 두 배 많은 기록이 들어가고, 여러 줄로 쌓으면 점이 이어져 면적 그래프가 된다.
# 왼쪽 열 점과 오른쪽 열 점을 아래에서부터 위로 차례로 적은 비트다
BRAILLE_LEFT = (0x40, 0x04, 0x02, 0x01)
BRAILLE_RIGHT = (0x80, 0x20, 0x10, 0x08)
BRAILLE_BASE = 0x2800
GRAPH_BASELINE = "⣀"  # 값이 0 인 자리에 까는 바닥 선
# 그래프 높이(줄 수)를 창 높이로 정한다. (이 줄 수 이상이면, 이만큼). 낮으면 안 그리고 CPU 줄 끝 추이로 대신한다
GRAPH_HEIGHTS = ((34, 3), (27, 2))
# 측정값 하나가 차지하는 점 열 수. 1 이면 뾰족한 값이 열 사이를 지날 때 높이가 반으로 꺼졌다 살아나며 들썩인다
GRAPH_DOTS_PER_SAMPLE = 2
GRAPH_FRAME_SECONDS = 1 / 15  # 그래프가 흘러가게 화면을 다시 그리는 간격. 점 열 하나 미는 데 갱신 주기 절반이 걸려 이 정도면 매끄럽다

# 측정값이 바뀌면 막대와 숫자를 툭 바꾸지 않고 이만큼(초)에 걸쳐 미끄러지게 옮긴다
TWEEN_SECONDS = 0.45
FRAME_SECONDS = 1 / 30  # 옮기는 동안 화면을 다시 그리는 간격

# 값 급등 표시. 줄의 CPU 가 지난번보다 코어 몇 % 어치 넘게 뛰면 CPU% 칸이 번쩍였다가 식는다.
# 기기 전체 % 로 재면 코어가 많은 기기에서는 늘 작게 뛰어서 코어 기준으로 본다 (50 = 코어 반 개)
FLASH_JUMP = 50
FLASH_SECONDS = 1.4
FLASH_RGB = (255, 176, 32)  # 번쩍일 때 바탕색. 식으면서 점점 어두워진다

# 종료시킨 줄이 사라지는 연출. 빨갛게 번쩍인 뒤 글자가 하나씩 부서져 흩어진다
VANISH_FLASH = 0.12
VANISH_SECONDS = 0.75
VANISH_GLYPHS = "▓▒░·"
VANISH_GLYPHS_ASCII = "#=-."
KILL_REFRESH_DELAY = 0.15  # 종료시킨 뒤 목록을 다시 읽기까지 기다리는 초

# 프로세스 표의 '해독' 연출. 갱신으로 바뀐 글자만 무작위 글자로 깜빡이다가 왼쪽부터 제 글자로 굳는다
LIST_DECODE_SECONDS = 0.4
LIST_NOISE = "0123456789abcdef#%&*+=?"
LIST_NOISE_RGB = (64, 150, 170)
LIST_SETTLE_RGB = (235, 250, 255)  # 막 굳은 글자가 잠깐 띠는 색
LIST_SETTLE = 0.1  # 굳은 뒤 그 색으로 남는 동안 (진행 비율)

# 표가 잠겼을 때 두르는 테두리. 잠기는 순간 하얗게 번쩍였다가 이 색으로 가라앉는다
LOCK_RGB = (245, 180, 60)
LOCK_SETTLE_SECONDS = 0.35

# 상세 창. 뒤 화면을 이 비율까지 어둡게 하고, 여는 동안 창이 가운데에서 좌우로 펼쳐진다
DETAIL_DIM = 0.32
DETAIL_SHADOW = 0.12  # 창 그림자 자리는 더 어둡게
DETAIL_OPEN_SECONDS = 0.18
DETAIL_MAX_BODY = 16  # 상세 창 본문 최대 줄 수. 묶은 줄의 프로세스 목록이 길어도 이만큼에서 끊는다
DETAIL_BG = (28, 32, 40)
DETAIL_BORDER = (88, 108, 138)
DETAIL_TITLE = (125, 211, 252)
DETAIL_LABEL = (128, 136, 150)
DETAIL_TEXT = (226, 232, 240)
DETAIL_DIM_TEXT = (100, 108, 122)
DETAIL_KEY = (222, 226, 232)  # 조작 키 바탕
# 전체 CPU 에서 프로세스 몫을 뺀 나머지가 이만큼(%p) 넘으면 CPU 줄에 띄운다. 평소에도
# 인터럽트 처리 같은 게 몇 %p 는 남아서, 그보다 확실히 클 때만 보이게 한다
UNLISTED_WARN = 10.0

# 막대 색이 바뀌는 자리. (비율, RGB). 사이는 섞어서 칠한다. 칸이 차오를수록 짙은 청록 → 초록 →
# 노랑 → 빨강으로 번져서 막대 끝 색만 봐도 얼마나 찼는지 안다. 노랑·빨강이 짙어지는 자리는
# level_color 의 기준(60%, 85%)과 맞춘다. 256색은 초록 칸이 몇 개 없어 짧은 막대가 단색이 된다
BAR_STOPS = (
    (0.00, (13, 110, 86)),
    (0.30, (34, 197, 94)),
    (0.52, (163, 230, 53)),
    (0.66, (250, 204, 21)),
    (0.85, (249, 115, 22)),
    (1.00, (239, 68, 68)),
)
BAR_FILL = "━"  # 줄 높이를 다 채우는 █ 는 위아래 막대가 맞붙어 한 덩어리로 보인다
BAR_HALF = "╸"  # 반 칸
# 빈 칸은 가는 선. 색이 없어도(파이프·파일) 굵은 선과 모양으로 갈린다
BAR_TRACK = "─"
BAR_TRACK_COLOR = f"{ESC}[38;5;239m"
BAR_DIM_START = 0.55  # 막대 첫 칸의 밝기. 끝으로 갈수록 밝아져서 짧은 막대도 그라데이션이 보인다
# 메모리 막대에서 사용 중 뒤에 잇는 캐시 몫. 차분한 파랑이라 '쓰는 중' 과 갈린다.
# 메모리 줄 옆의 '캐시 N GB' 글자도 같은 색으로 칠해 범례 노릇을 하게 한다
CACHE_COLOR = f"{ESC}[38;2;74;120;160m"
# 네트워크 받기·보내기 색. 막대 반쪽과 옆의 속도 글자를 같은 색으로 칠해 짝을 맞춘다
NET_DOWN = f"{ESC}[38;2;86;176;235m"
NET_UP = f"{ESC}[38;2;196;136;235m"
NET_FLOOR = 1024  # 네트워크 막대 눈금의 바닥(바이트/초). 이보다 적으면 비어 보인다

# 시작 화면 로고. 글자마다 따로 두고 한 칸씩 띄워 이어 붙인다
LOGO = (
    ("██╗    ██╗", "██║    ██║", "██║ █╗ ██║", "██║███╗██║", "╚███╔███╔╝", " ╚══╝╚══╝ "),
    ("███████╗", "██╔════╝", "███████╗", "╚════██║", "███████║", "╚══════╝"),
    (" ██████╗", "██╔════╝", "██║     ", "██║     ", "╚██████╗", " ╚═════╝"),
)
# 위 선 글자도 옛 콘솔에서는 두 칸으로 그려져 로고가 뭉개진다. 그때 쓰는 영문판
LOGO_ASCII = (
    (r"__        __", r"\ \      / /", r" \ \ /\ / / ", r"  \ V  V /  ", r"   \_/\_/   "),
    (r" ____  ", r"/ ___| ", r"\___ \ ", r" ___) |", r"|____/ "),
    (r"  ____ ", r" / ___|", r"| |    ", r"| |___ ", r" \____|"),
)
# 로고 글자색. 왼쪽에서 오른쪽으로 하늘색 → 파랑 → 보라. 그림자(선 글자)는 가라앉힌다
LOGO_COLORS = tuple(f"{ESC}[38;5;{c}m" for c in (87, 81, 75, 69, 105, 141))
LOGO_SHADOW = f"{ESC}[38;5;60m"
SPLASH_SECONDS = 1.0  # 시작 로고를 띄워 두는 시간. 그사이 첫 측정을 끝내 첫 화면부터 값이 나온다
# 로고 '해독' 연출. 처음 이만큼(초)에 걸쳐 무작위 글자가 제 글자로 굳는다. 나머지 시간은 다 된 로고를 보여준다
LOGO_DECODE_SECONDS = 0.65
LOGO_NOISE = "▓▒░█▚▞▙▟▛▜"
LOGO_NOISE_ASCII = "#%&@$*+=?"
LOGO_NOISE_LEAD = 0.3  # 굳기 이만큼 전부터 무작위 글자로 깜빡이기 시작한다 (해독 진행 비율)
LOGO_FLASH = 0.08  # 굳은 직후 하얗게 번쩍이는 동안 (해독 진행 비율)
LOGO_NOISE_COLOR = f"{ESC}[38;2;64;150;170m"
LOGO_FLASH_COLOR = f"{ESC}[38;2;235;250;255m"
LOGO_JITTER = tuple(random.Random(7).random() for _ in range(97))  # 칸마다 굳는 때를 어긋나게 할 고정 난수
# 나갈 때 연출. 옛 브라운관 TV 를 끄듯 화면이 위아래로 눌려 빛나는 가로줄 하나가 되고,
# 그 줄이 가운데 한 점으로 줄어든 뒤 꺼진다. 단계마다 걸리는 초
OUTRO_SQUEEZE = 0.24
OUTRO_SHRINK = 0.2
OUTRO_FADE = 0.16
OUTRO_LINE = (235, 250, 255)  # 눌린 줄의 색. 줄어들수록 로고 하늘색으로 식는다
OUTRO_EMBER = (95, 215, 255)

# 옛 콘솔(conhost)을 한중일 코드 페이지로 쓰면 █ · … 같은 '폭이 애매한' 글자를
# 두 칸으로 그려서 표가 통째로 어긋난다. 그럴 때 한 칸짜리 영문 기호로 바꿔 그린다
ASCII_MAP = str.maketrans({
    "█": "#", "·": ".", "…": "~", "–": "-", "—": "-", "─": "-",
    "›": ">", "↑": "^", "↓": "v", "▼": "v",
    "▁": "_", "▂": ".", "▃": ":", "▄": "-", "▅": "=", "▆": "+", "▇": "*",
})
USE_ASCII = False
# 작업 표시줄 아이콘에 CPU 막대를 띄우는가. Windows Terminal 이 알아듣는 OSC 9;4 를 쓴다.
# 다른 터미널 몇몇(WezTerm 등)은 OSC 9 를 알림 띄우기로 써서, 자기 이름을 밝힌 터미널에는 안 보낸다
TASKBAR = False


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


class SYSTEM_PROCESSOR_PERFORMANCE_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("IdleTime", ctypes.c_longlong),
        ("KernelTime", ctypes.c_longlong),  # 유휴 시간이 들어 있다
        ("UserTime", ctypes.c_longlong),
        ("DpcTime", ctypes.c_longlong),
        ("InterruptTime", ctypes.c_longlong),
        ("InterruptCount", wintypes.ULONG),
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
kernel32.GetConsoleWindow.restype = wintypes.HWND
kernel32.GetConsoleTitleW.argtypes = [wintypes.LPWSTR, wintypes.DWORD]
kernel32.GetConsoleTitleW.restype = wintypes.DWORD
kernel32.SetConsoleTitleW.argtypes = [wintypes.LPCWSTR]
kernel32.SetConsoleTitleW.restype = wintypes.BOOL
user32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
user32.GetClassNameW.restype = ctypes.c_int
kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
kernel32.OpenProcess.restype = wintypes.HANDLE
kernel32.TerminateProcess.argtypes = [wintypes.HANDLE, wintypes.UINT]
kernel32.TerminateProcess.restype = wintypes.BOOL
kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
kernel32.QueryFullProcessImageNameW.argtypes = [
    wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)
]
kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL
kernel32.CloseHandle.restype = wintypes.BOOL
iphlpapi.GetExtendedTcpTable.argtypes = [
    ctypes.c_void_p, ctypes.POINTER(wintypes.DWORD), wintypes.BOOL,
    wintypes.ULONG, ctypes.c_int, wintypes.ULONG,
]
iphlpapi.GetExtendedTcpTable.restype = wintypes.DWORD
iphlpapi.GetIfTable2.argtypes = [ctypes.POINTER(ctypes.c_void_p)]
iphlpapi.GetIfTable2.restype = wintypes.DWORD
iphlpapi.FreeMibTable.argtypes = [ctypes.c_void_p]
iphlpapi.FreeMibTable.restype = None

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
SYSTEM_PROCESSOR_PERFORMANCE_INFO = 8
ERROR_ACCESS_DENIED = 5
ERROR_INVALID_PARAMETER = 87
ERROR_INSUFFICIENT_BUFFER = 122
PROCESS_TERMINATE = 0x0001
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
FILETIME_UNIX_EPOCH = 116444736000000000  # 1601 년부터 1970 년까지를 100ns 로 센 값
WM_CLOSE = 0x0010
GW_OWNER = 4
AF_INET, AF_INET6 = 2, 23
TCP_TABLE_OWNER_PID_LISTENER = 3
# MIB_IF_ROW2 한 줄의 크기와, 쓰는 칸의 위치(바이트). 구조가 커서 필요한 칸만 꺼내 읽는다
IF_ROW2_SIZE = 1352
IF_ALIAS_AT, IF_ALIAS_LEN = 28, 514
IF_TYPE_AT = 1128
IF_FLAGS_AT = 1152  # 첫 비트가 실제 장치, 둘째 비트가 필터 드라이버
IF_STATE_AT = 1156  # 동작 상태, 관리 상태, 연결 상태가 차례로 있다
IF_SPEED_AT = 1192  # 보내기·받기 링크 속도(bps), 바로 뒤에 받은 바이트
IF_OUT_OCTETS_AT = 1280
IF_TYPE_LOOPBACK = 24
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
    """{pid: (생성 시각, 누적 CPU 초, 개인 작업 집합, 작업 집합, 이름, 스레드 수, 핸들 수, 부모 PID)} 스냅샷.

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
                info.NumberOfThreads,
                info.HandleCount,
                info.InheritedFromUniqueProcessId or 0,
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


def core_times() -> list:
    """코어마다 (유휴, 전체) 누적 시간. 못 읽으면 빈 목록.

    코어가 64개를 넘는 기기는 윈도우가 코어를 묶음으로 나누는데, 이 값은 wsc 가 도는
    묶음 것만 준다. 그런 기기에서는 일부 코어만 보인다.
    """
    entry = ctypes.sizeof(SYSTEM_PROCESSOR_PERFORMANCE_INFORMATION)
    buf, _ = query_system(SYSTEM_PROCESSOR_PERFORMANCE_INFO, entry * NCPU)
    if buf is None:
        return []
    cores = (SYSTEM_PROCESSOR_PERFORMANCE_INFORMATION * NCPU).from_buffer(buf)
    return [(c.IdleTime, c.KernelTime + c.UserTime) for c in cores if c.KernelTime + c.UserTime]


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


def sample_network() -> dict:
    """{LUID: (받은 바이트, 보낸 바이트, 받기 링크 bps, 보내기 링크 bps, 이름)} — 연결된 실제 장치만.

    인터페이스 목록에는 같은 랜카드가 필터 드라이버(방화벽·QoS)마다 한 번씩 더 나오고,
    WSL·Hyper-V 의 가상 어댑터도 있다. 가상 어댑터를 지나는 트래픽은 결국 실제 랜카드로도
    나가서, 다 더하면 같은 바이트를 두 번 세게 된다. 그래서 실제 장치만 더한다.
    """
    table = ctypes.c_void_p()
    if iphlpapi.GetIfTable2(ctypes.byref(table)) != 0 or not table.value:
        return {}
    found = {}
    try:
        count = ctypes.c_ulong.from_address(table.value).value
        for i in range(count):
            # 표 머리의 개수 칸 뒤로 8바이트 정렬을 맞춰 줄이 이어진다
            row = ctypes.string_at(table.value + 8 + i * IF_ROW2_SIZE, IF_ROW2_SIZE)
            flags = row[IF_FLAGS_AT]
            oper, _, media = struct.unpack_from("<III", row, IF_STATE_AT)
            if_type = struct.unpack_from("<I", row, IF_TYPE_AT)[0]
            # 실제 장치이고, 필터가 아니고, 켜져서 연결된 것만
            if not flags & 1 or flags & 2 or oper != 1 or media != 1:
                continue
            if if_type == IF_TYPE_LOOPBACK:
                continue
            tx_speed, rx_speed, rx_bytes = struct.unpack_from("<QQQ", row, IF_SPEED_AT)
            tx_bytes = struct.unpack_from("<Q", row, IF_OUT_OCTETS_AT)[0]
            alias = row[IF_ALIAS_AT : IF_ALIAS_AT + IF_ALIAS_LEN].decode("utf-16-le", "replace")
            luid = struct.unpack_from("<Q", row, 0)[0]
            found[luid] = (rx_bytes, tx_bytes, rx_speed, tx_speed, alias.split("\0")[0])
    finally:
        iphlpapi.FreeMibTable(table)
    return found


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
    덧붙일 말은 경고일 때만 있다. 평소에 늘 떠 있으면 눈이 무뎌져 정작 필요할 때 안 읽힌다.
    무엇이 기준을 넘었는지 숫자로 밝히고, 바로 할 수 있는 일을 키와 함께 적는다
    """
    commit_pct = mem["commit"] / mem["commit_limit"] * 100 if mem["commit_limit"] else 0.0
    # 둘 중 더 높은 쪽이 판단 근거다
    if commit_pct > mem["load"]:
        reason = f"커밋 {commit_pct:.0f}%"
    else:
        reason = f"사용률 {mem['load']}%"
    worst = max(mem["load"], commit_pct)
    if worst >= 95:
        return ("위험", RED, f"{reason} — 새 프로그램이 안 열리거나 멈출 수 있음. m 정렬 후 큰 것부터 종료")
    if worst >= 85:
        return ("주의", YELLOW, f"{reason} — m 으로 메모리순 정렬해 안 쓰는 프로그램 정리 권장")
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


def process_path(pid: int) -> str:
    """실행 파일의 전체 경로. 시스템 프로세스처럼 열어 볼 권한이 없으면 빈 문자열.

    '제한된 조회' 권한만 달라고 해서, 관리자 권한이 없어도 내 프로세스는 대부분 열린다.
    """
    handle = kernel32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
    if not handle:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(1024)
        size = wintypes.DWORD(len(buf))
        if kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
            return buf.value
        return ""
    finally:
        kernel32.CloseHandle(handle)


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


def human_rate(n: float) -> str:
    """초당 바이트. 폭이 8칸을 넘지 않게 자릿수를 맞춘다. 숫자가 바뀔 때 줄이 들썩이지 않게."""
    if n >= 1024**3:
        return f"{n / 1024**3:.1f}GB/s"
    if n >= 100 * 1024**2:
        return f"{n / 1024**2:.0f}MB/s"
    if n >= 1024**2:
        return f"{n / 1024**2:.1f}MB/s"
    if n >= 1024:
        return f"{n / 1024:.0f}KB/s"
    return f"{int(n)}B/s"


def human_bps(bits: int) -> str:
    """링크 속도. 랜카드·공유기 표기처럼 비트 단위·1000 배수로 적는다."""
    if bits >= 10**9:
        return f"{bits / 10**9:.1f}".rstrip("0").rstrip(".") + "Gbps"
    return f"{bits / 10**6:.0f}Mbps"


def log_frac(rate: float, link: float) -> float:
    """네트워크 막대 길이. 회선 속도 대비를 로그 눈금으로 잰다.

    그대로 나누면 1Gbps 회선에서 수십 KB/s 는 0.01% 라 평소엔 막대가 늘 비어 보인다.
    로그로 재면 1KB/s 는 0, 1MB/s 는 절반쯤, 회선을 꽉 채우면 끝까지 찬다.
    """
    if rate <= 0 or link <= NET_FLOOR:
        return 0.0
    return min(1.0, math.log10(1 + rate / NET_FLOOR) / math.log10(1 + link / NET_FLOOR))


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


def bar_rgb(frac: float) -> tuple:
    """비율 하나에 맞는 막대 색. BAR_STOPS 사이를 섞는다."""
    frac = max(0.0, min(1.0, frac))
    for (lo, lo_rgb), (hi, hi_rgb) in zip(BAR_STOPS, BAR_STOPS[1:]):
        if frac <= hi:
            t = (frac - lo) / (hi - lo)
            return tuple(round(a + (b - a) * t) for a, b in zip(lo_rgb, hi_rgb))
    return BAR_STOPS[-1][1]


def rgb(color: tuple, bright: float = 1.0) -> str:
    return f"{ESC}[38;2;{';'.join(str(round(c * bright)) for c in color)}m"


def bar_color(frac: float) -> str:
    """추이 칸 하나의 색. 그 칸이 나타내는 비율로 정한다."""
    return rgb(bar_rgb(frac))


def draw_bar(frac: float, width: int, color: str = "", extra: float = 0.0) -> str:
    """━━━━╸───── 모양 막대. width 칸이다.

    색을 따로 주지 않으면 칸마다 제 자리의 색을 칠한다. 한 가지 색으로 칠하면
    60% 와 84% 가 똑같은 노랑이라 얼마나 찼는지 막대 길이로만 갈라야 한다.
    extra 는 frac 뒤에 이어 흐리게 칠할 둘째 몫이다 (메모리 막대의 캐시).
    """
    frac = max(0.0, min(1.0, frac))
    end = max(frac, min(1.0, frac + extra))
    if USE_ASCII:
        # 선 글자는 옛 콘솔에서 두 칸으로 그려진다. 테두리를 쳐서 막대 길이가 보이게 한다
        inner = max(1, width - 2)
        full = int(frac * inner)
        more = max(full, int(end * inner))
        return (
            f"{GRAY}[{RESET}{color or level_color(frac)}{'#' * full}{RESET}"
            f"{CACHE_COLOR}{'=' * (more - full)}{RESET}"
            f"{DIM}{'.' * (inner - more)}{RESET}{GRAY}]{RESET}"
        )
    # 반 칸 단위로 센다. 끝이 반 칸에 걸리면 ╸ 로 그린다
    main_h = round(frac * width * 2)
    end_h = max(main_h, round(end * width * 2))
    main_cells = (main_h + 1) // 2
    out, last = [], ""
    for i in range(width):
        left, right = 2 * i, 2 * i + 1
        if left < main_h:
            if color:
                cell_color = color
            else:
                # 제 자리의 색에, 막대 끝으로 갈수록 밝아지는 정도를 곱한다
                ramp = BAR_DIM_START + (1 - BAR_DIM_START) * (i + 1) / main_cells
                cell_color = rgb(bar_rgb((i + 0.5) / width), ramp)
            glyph = BAR_FILL if right < end_h else BAR_HALF
        elif left < end_h:
            cell_color, glyph = CACHE_COLOR, BAR_FILL if right < end_h else BAR_HALF
        else:
            cell_color, glyph = BAR_TRACK_COLOR, BAR_TRACK
        if cell_color != last:  # 색이 바뀌는 칸에서만 색 코드를 넣는다
            out.append(cell_color)
            last = cell_color
        out.append(glyph)
    out.append(RESET)
    return "".join(out)


def draw_cores(pcts: list, width: int) -> str:
    """코어마다 한 칸씩 ▁▂▃▅▇ 높이와 색으로. 칸이 모자라면 이웃 코어를 묶어 그중 큰 값을 그린다.

    코어가 적어 자리가 넉넉하면 한 칸씩 띄워 그린다. 붙여 그리면 막대그래프처럼 뭉쳐 보인다.
    """
    per = -(-len(pcts) // max(1, width))  # 한 칸에 담을 코어 수 (올림)
    cells = [max(pcts[i:i + per]) for i in range(0, len(pcts), per)]
    gap = " " if len(cells) * 2 - 1 <= width else ""
    out = []
    for v in cells:
        level = min(len(SPARKS) - 1, int(v / 100.0 * len(SPARKS)))
        out.append(f"{bar_color(v / 100.0)}{SPARKS[level]}")
    return gap.join(out) + RESET


def draw_spark(values, width: int) -> str:
    """최근 CPU% 를 ▁▂▃▅▇ 한 줄로. 눈금은 0~100% 고정이다.

    가장 높은 값에 맞춰 늘리면 1~2% 흔들림도 산처럼 보여서 겁만 준다.
    """
    out = []
    for v in list(values)[-width:]:
        level = min(len(SPARKS) - 1, int(v / 100.0 * len(SPARKS)))
        out.append(f"{bar_color(v / 100.0)}{SPARKS[level]}")
    return "".join(out) + RESET


def graph_points(values: list, stamps: list, now: float, count: int) -> list:
    """그래프의 점 열 count 개에 그릴 값. 왼쪽부터 차례로, 기록이 닿지 않는 열은 None.

    측정값 하나가 점 열 GRAPH_DOTS_PER_SAMPLE 개를 차지하고, 그 사이는 앞뒤 값을 이어 채운다.
    오른쪽 끝은 직전 값에서 최신 값으로, 측정 간격에 걸쳐 시각에 맞춰 다가간다.
    그래서 다음 값이 올 때쯤 그래프가 딱 한 측정만큼 밀려 있어, 새 값이 와도 끊기지 않고 이어진다.
    """
    last = len(values) - 1
    if last < 1:
        return [None] * count
    gap = stamps[-1] - stamps[-2]
    progress = min(1.0, max(0.0, (now - stamps[-1]) / gap)) if gap > 0 else 1.0
    head = last - 1 + progress  # 오른쪽 끝 열이 가리키는 기록 위치 (소수)
    out = []
    for x in range(count):
        q = head - x / GRAPH_DOTS_PER_SAMPLE
        if q < 0:
            out.extend([None] * (count - x))
            break
        i = int(q)
        t = q - i
        out.append(values[i] if i >= last else values[i] + (values[i + 1] - values[i]) * t)
    out.reverse()
    return out


def draw_graph(points: list, width: int, height: int) -> list:
    """CPU% 를 점자 글자 면적 그래프로. height 줄, width 칸이고 한 칸에 점 열이 둘 들어간다.

    points 는 점 열마다의 값이다 (graph_points). 눈금은 추이처럼 0~100% 고정이다.
    색은 높이로 칠한다. 아래는 초록, 위로 갈수록 노랑·빨강이라 꼭대기 색만 봐도 얼마나 튀었는지 안다.
    """
    dots = height * 4
    levels = [
        None if v is None else max(1, round(v / 100.0 * dots)) if v > 0.5 else 0
        for v in points
    ]
    rows = []
    for row in range(height):
        floor = (height - 1 - row) * 4  # 이 줄 맨 아래 점이 몇 번째 점인가
        color = rgb(bar_rgb((floor + 2) / dots))
        out, last = [], ""
        for i in range(width):
            pair = levels[2 * i], levels[2 * i + 1]
            bits = 0
            for level, column in zip(pair, (BRAILLE_LEFT, BRAILLE_RIGHT)):
                for k in range(max(0, min(4, (level or 0) - floor))):
                    bits |= column[k]
            if bits:
                glyph, cell_color = chr(BRAILLE_BASE + bits), color
            elif row == height - 1 and pair != (None, None):
                glyph, cell_color = GRAPH_BASELINE, BAR_TRACK_COLOR
            else:
                glyph, cell_color = " ", ""
            if cell_color and cell_color != last:
                out.append(cell_color)
                last = cell_color
            out.append(glyph)
        out.append(RESET)
        rows.append("".join(out))
    return rows


class Tween:
    """측정값 사이를 부드럽게 잇는다. 새 값이 오면 지금 보이는 값에서 출발해 TWEEN_SECONDS 동안 다가간다.

    측정은 몇 초에 한 번이지만 화면은 그사이 여러 번 그려서, 막대가 툭툭 끊기지 않고 미끄러진다.
    꺼 두면 늘 새 값을 바로 돌려준다 (파일로 내보낼 때).
    """

    def __init__(self):
        self.enabled = False
        self.items = {}  # {이름: (출발 값, 목표 값, 출발 시각)}

    def set(self, name, target: float, now: float):
        # 처음 보는 값은 0 에서 차오른다. 첫 화면이 뜰 때 막대가 한꺼번에 채워지는 연출이 된다
        if not self.enabled:
            start = target
        else:
            start = self.get(name, now) if name in self.items else 0.0
        self.items[name] = (start, target, now)

    def get(self, name, now: float, default: float = 0.0) -> float:
        item = self.items.get(name)
        if item is None:
            return default
        start, target, began = item
        t = (now - began) / TWEEN_SECONDS
        if not self.enabled or t >= 1.0:
            return target
        t = max(0.0, t)
        return start + (target - start) * (1 - (1 - t) ** 3)  # 처음엔 빠르고 끝에서 살며시 멈춘다

    def busy(self, now: float) -> bool:
        return self.enabled and any(
            now - began < TWEEN_SECONDS and start != target
            for start, target, began in self.items.values()
        )


# ── 화면 겹치기 (상세 창) ───────────────────────────────────────
# 상세 창을 띄울 때 뒤 화면을 어둡게 다시 칠하고 그 위에 창을 얹는다. 색 코드가 섞인 줄을
# 칸마다 (글자, 모양) 으로 풀어 놓아야 어느 칸이든 색을 바꾸거나 덮어쓸 수 있다.
# 모양은 (글자색, 바탕색, 굵게) 이고 색은 (R, G, B) 또는 None(터미널 기본색) 이다
SGR_RE = re.compile(r"\x1b\[([0-9;]*)m")
DEFAULT_FG = (204, 204, 204)  # 색을 안 준 글자를 어둡게 칠할 때 기준으로 삼는 색
XTERM_BASE = (
    (0, 0, 0), (205, 49, 49), (13, 188, 121), (229, 229, 16), (36, 114, 200), (188, 63, 188),
    (17, 168, 205), (229, 229, 229), (102, 102, 102), (241, 76, 76), (35, 209, 139),
    (245, 245, 67), (59, 142, 234), (214, 112, 214), (41, 184, 219), (255, 255, 255),
)


def xterm_rgb(n: int) -> tuple:
    """256색 번호를 RGB 로."""
    if n < 16:
        return XTERM_BASE[n]
    if n < 232:
        n -= 16
        steps = (0, 95, 135, 175, 215, 255)
        return steps[n // 36], steps[n // 6 % 6], steps[n % 6]
    gray = 8 + 10 * (n - 232)
    return gray, gray, gray


def apply_sgr(style: tuple, params: str) -> tuple:
    """색 코드 하나를 모양에 적용한다. wsc 가 쓰는 것만 알아듣는다."""
    fg, bg, bold = style
    codes = [int(c) if c else 0 for c in params.split(";")] if params else [0]
    i = 0
    while i < len(codes):
        c = codes[i]
        if c == 0:
            fg, bg, bold = None, None, False
        elif c == 1:
            bold = True
        elif c == 22:
            bold = False
        elif c == 2:
            fg = tuple(round(v * 0.6) for v in (fg or DEFAULT_FG))  # 흐리게는 색을 낮춰 흉내 낸다
        elif c in (38, 48) and i + 1 < len(codes):
            if codes[i + 1] == 5 and i + 2 < len(codes):
                color = xterm_rgb(codes[i + 2])
                i += 2
            elif codes[i + 1] == 2 and i + 4 < len(codes):
                color = tuple(codes[i + 2:i + 5])
                i += 4
            else:
                color = None
            if c == 38:
                fg = color
            else:
                bg = color
        elif c == 39:
            fg = None
        elif c == 49:
            bg = None
        i += 1
    return fg, bg, bold


def to_cells(line: str, cols: int) -> list:
    """색 코드가 섞인 줄을 cols 칸의 [글자, 모양] 목록으로. 두 칸 글자 뒤 칸은 글자가 '' 다."""
    cells = []
    style = (None, None, False)
    pos = 0
    while pos < len(line) and len(cells) < cols:
        m = SGR_RE.match(line, pos)
        if m:
            style = apply_sgr(style, m.group(1))
            pos = m.end()
            continue
        if line[pos] == "\x1b":  # 색이 아닌 제어 문자는 건너뛴다
            m = ANSI_RE.match(line, pos)
            pos = m.end() if m else pos + 1
            continue
        ch = line[pos]
        pos += 1
        w = dwidth(ch)
        if w == 0:
            continue
        if len(cells) + w > cols:
            break
        cells.append([ch, style])
        if w == 2:
            cells.append(["", style])
    while len(cells) < cols:
        cells.append([" ", (None, None, False)])
    return cells


def sgr_of(style: tuple) -> str:
    fg, bg, bold = style
    parts = ["0"]
    if bold:
        parts.append("1")
    if fg:
        parts.append("38;2;%d;%d;%d" % fg)
    if bg:
        parts.append("48;2;%d;%d;%d" % bg)
    return f"{ESC}[{';'.join(parts)}m"


def from_cells(cells: list) -> str:
    out, last = [], None
    for ch, style in cells:
        if ch == "":
            continue
        if style != last:
            out.append(sgr_of(style))
            last = style
        out.append(ch)
    out.append(RESET)
    return "".join(out)


def darken(style: tuple, factor: float) -> tuple:
    fg, bg, bold = style
    fg = tuple(round(v * factor) for v in (fg or DEFAULT_FG))
    bg = tuple(round(v * factor) for v in bg) if bg else None
    return fg, bg, bold


def put_text(cells: list, col: int, text: str, style: tuple):
    """cells 의 col 칸부터 text 를 덮어쓴다. 반쪽만 덮인 두 칸 글자는 빈칸으로 바꾼다."""
    if 0 < col < len(cells) and cells[col][0] == "":
        cells[col - 1][0] = " "
    for ch in text:
        w = dwidth(ch)
        if w == 0:
            continue
        if col + w > len(cells):
            break
        cells[col] = [ch, style]
        if w == 2:
            cells[col + 1] = ["", style]
        col += w
    if col < len(cells) and cells[col][0] == "":
        cells[col][0] = " "


def mid_trunc(s: str, width: int) -> str:
    """가운데를 … 로 줄인다. 경로는 앞(드라이브)과 끝(파일 이름)이 다 중요하다."""
    if dwidth(s) <= width:
        return s
    if width < 5:
        return dtrunc(s, width)
    keep_tail = width // 2
    tail, used = "", 0
    for ch in reversed(s):
        if used + dwidth(ch) > keep_tail:
            break
        tail = ch + tail
        used += dwidth(ch)
    return dtrunc(s, width - used) + tail  # 앞쪽은 늘 잘리므로 끝에 … 가 붙어 있다


def ease_out(t: float) -> float:
    t = max(0.0, min(1.0, t))
    return 1 - (1 - t) ** 3


def vanish_line(text: str, age: float) -> str:
    """종료시킨 줄이 사라지는 모습. age 는 사라지기 시작한 뒤 흐른 초.

    처음 VANISH_FLASH 초는 줄 전체가 빨갛게 번쩍인다. 그 뒤로는 글자마다 정해진 때에
    ▓▒░· 로 부서지다 빈칸이 된다. 왼쪽부터 무너지되 칸마다 조금씩 어긋나 흩어지듯 보인다
    """
    if age < VANISH_FLASH:
        return f"{ESC}[48;2;200;45;45m{ESC}[38;2;255;255;255m{BOLD}{text}{RESET}"
    p = (age - VANISH_FLASH) / (VANISH_SECONDS - VANISH_FLASH)
    glyphs = VANISH_GLYPHS_ASCII if USE_ASCII else VANISH_GLYPHS
    crumble = 0.18  # 한 글자가 부서지는 동안 (진행 비율)
    out, last = [], ""
    n = max(1, len(text.rstrip()))  # 이름 뒤 빈칸까지 세면 글자가 너무 일찍 다 부서진다
    for i, ch in enumerate(text):
        w = dwidth(ch)
        if ch == " " or w == 0:
            out.append(ch)
            continue
        at = 0.8 * (0.55 * i / n + 0.45 * LOGO_JITTER[(i * 37) % len(LOGO_JITTER)])
        if p < at:
            # 아직 남은 글자. 시간이 갈수록 붉은빛이 사그라진다
            fade = p / at
            color = rgb((255 - round(110 * fade), 110 - round(60 * fade), 110 - round(60 * fade)))
            glyph = ch
        elif p < at + crumble:
            k = int((p - at) / crumble * len(glyphs))
            color = rgb((190, 60, 50))
            glyph = glyphs[min(k, len(glyphs) - 1)] * w  # 두 칸 글자 자리는 두 칸을 채워 폭을 지킨다
        else:
            out.append(" " * w)
            continue
        if color != last:
            out.append(color)
            last = color
        out.append(glyph)
    out.append(RESET)
    return "".join(out)


def decode_spots(old: str, new: str, width: int) -> list:
    """표 한 줄이 바뀔 때 해독 연출을 할 칸들. [(칸 위치, 두 칸 글자인가, 굳는 때)].

    글자가 같은 칸은 건드리지 않는다. 숫자 몇 자리만 바뀌면 그 자리만 깜빡인다.
    굳는 때는 왼쪽일수록 이르고 칸마다 조금씩 어긋난다 (0~1, 연출 진행 비율).
    """
    before, after = to_cells(old, width), to_cells(new, width)
    last = max((i for i, c in enumerate(after) if c[0] not in (" ", "")), default=0) or 1
    spots = []
    for c in range(1, width):  # 맨 앞 칸은 고른 줄 표시(›) 자리라 뺀다
        ch = after[c][0]
        if ch == "" or (ch == before[c][0] and (c + 1 >= width or after[c + 1][0] == before[c + 1][0])):
            continue
        if ch == " " and before[c][0] in (" ", ""):
            continue
        wide = c + 1 < width and after[c + 1][0] == ""
        at = 0.65 * min(1.0, c / last) + 0.35 * LOGO_JITTER[(c * 53) % len(LOGO_JITTER)]
        spots.append((c, wide, at * (1 - LIST_SETTLE)))
    return spots


def decode_line(line: str, spots: list, progress: float, width: int) -> str:
    """해독 중인 표 한 줄. 아직 안 굳은 칸은 무작위 글자로, 막 굳은 칸은 밝게 그린다."""
    cells = to_cells(line, width)
    noise_style = (LIST_NOISE_RGB, None, False)
    for c, wide, at in spots:
        if progress < at:
            glyph = random.choice(LIST_NOISE)
            cells[c] = [glyph, noise_style]
            if wide:
                cells[c + 1] = [random.choice(LIST_NOISE), noise_style]
        elif progress < at + LIST_SETTLE and cells[c][0] != " ":
            _, bg, bold = cells[c][1]
            cells[c][1] = (LIST_SETTLE_RGB, bg, bold)
            if wide:
                cells[c + 1][1] = (LIST_SETTLE_RGB, bg, bold)
    return from_cells(cells)


def human_age(seconds: float) -> str:
    """얼마나 오래됐는지. 상세 창의 시작 시각 옆에 붙인다."""
    minutes = int(seconds // 60)
    if minutes < 1:
        return "방금"
    if minutes < 60:
        return f"{minutes}분 전"
    hours, minutes = divmod(minutes, 60)
    if hours < 24:
        return f"{hours}시간 {minutes}분 전"
    days, hours = divmod(hours, 24)
    return f"{days}일 {hours}시간 전"


def filetime_local(ft: int):
    """FILETIME(1601 년부터 100ns) 을 지역 시각(struct_time)으로. 0 이면 None."""
    if ft <= FILETIME_UNIX_EPOCH:
        return None
    return time.localtime((ft - FILETIME_UNIX_EPOCH) / 1e7)


def logo_lines(reveal: float = 1.0) -> tuple:
    """색을 입힌 로고 줄 목록과 그 폭. 영문 기호 모드면 영문판을 쓴다.

    reveal 이 1 보다 작으면 '해독' 중인 모습을 그린다. 왼쪽부터 무작위 글자가 번갈아 깜빡이다가
    제 글자로 굳고, 굳는 순간 하얗게 번쩍인다. 부를 때마다 무작위 글자가 바뀌어 깜빡임이 된다
    """
    glyphs = LOGO_ASCII if USE_ASCII else LOGO
    rows = [" ".join(letter[i] for letter in glyphs) for i in range(len(glyphs[0]))]
    width = max(len(row) for row in rows)
    noise = LOGO_NOISE_ASCII if USE_ASCII else LOGO_NOISE
    out = []
    for r, row in enumerate(rows):
        parts, last = [], ""
        for col, ch in enumerate(row):
            if ch != " " and reveal < 1.0:
                # 이 칸이 굳는 때. 왼쪽일수록 이르고, 칸마다 조금씩 어긋나 물결처럼 번진다
                at = 0.7 * col / width + 0.3 * LOGO_JITTER[(r * 131 + col) % len(LOGO_JITTER)]
                if reveal < at - LOGO_NOISE_LEAD:
                    ch = " "
                elif reveal < at:
                    ch = random.choice(noise)
                    color = LOGO_NOISE_COLOR
                elif reveal < at + LOGO_FLASH:
                    color = LOGO_FLASH_COLOR
                else:
                    at = None
                if at is not None and ch != " ":
                    if color != last:
                        parts.append(color)
                        last = color
                    parts.append(ch)
                    continue
            if ch != " ":
                if ch == "█" or USE_ASCII:
                    color = LOGO_COLORS[col * len(LOGO_COLORS) // width]
                else:
                    color = LOGO_SHADOW
                if color != last:
                    parts.append(color)
                    last = color
            parts.append(ch)
        out.append("".join(parts) + RESET)
    return out, width


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
        self.unlisted_cpu = 0.0  # 전체 CPU 중 목록의 어느 프로세스에도 안 잡힌 몫
        self.cpu_hist = collections.deque(maxlen=CPU_HIST_MAX)  # 최근 전체 CPU%. 추이 그래프용
        self.cpu_hist_at = collections.deque(maxlen=CPU_HIST_MAX)  # 위 값을 잰 시각. 그래프를 시각에 맞춰 흘려 그린다
        # 화면에 그리는 값. 측정값을 따라 미끄러진다. 대화형 화면에서만 켠다
        self.tween = Tween()
        # 대화형 화면인가. 점자 그래프처럼 파일로 내보내면 깨지는 것은 이때만 그린다
        self.live = False
        self.graph_h = 0  # 지난번에 그린 추이 그래프 높이. 0 이면 그래프가 없어 계속 다시 그릴 필요가 없다
        self.prev_cores = []  # 지난번 코어별 (유휴, 전체) 누적 시간
        self.core_pct = []  # 코어별 사용률(%). 두 번 재기 전엔 빈 목록
        self.ready = False
        # 수집 결과는 여기 담아둔다. 키를 눌러 다시 그릴 때 또 읽지 않으려는 것
        self.mem = dict(EMPTY_MEMORY)
        self.pagefile = (0, 0)
        self.compressed = 0
        self.net_prev = {}  # 지난번 인터페이스별 누적 바이트. 차이로 속도를 낸다
        self.net_rate = None  # (받기, 보내기) 초당 바이트. 두 번 재기 전엔 None
        self.net_links = []  # [(이름, 받기 bps, 보내기 bps)] 지금 연결된 실제 장치
        self.interval_changed_at = 0.0  # 주기를 바꾼 직후 잠깐 강조하려고 기록
        self.latest_version = ""  # 새 버전 확인 결과. 별도 흐름에서 채운다
        # 프로세스 고르기와 종료 관련
        # 같은 이름의 프로세스를 한 줄로 합쳐 보는가. 크롬처럼 여러 개 띄우는 프로그램의 몫이 보인다.
        # 처음부터 묶어 둔다. 안 묶으면 표 위쪽이 같은 이름으로 도배돼 딴 프로그램이 밀려난다
        self.grouped = True
        # 줄 번호가 아니라 PID 로 기억한다. 순위가 바뀌어도 따라가게. 묶음 보기에서는 이름이다
        self.selected = None
        self.scroll = 0
        self.visible_rows = 1
        self.ports = {}  # {PID: [포트, ...]}
        self.procs = {}  # 마지막으로 읽은 sample_processes() 결과
        self.pending_kill = None  # 종료 확인을 기다리는 (PID, 이름, 생성 시각)
        self.status = ("", "", 0.0)  # (문구, 색, 띄운 시각)
        self.needs_refresh = False
        # 연출용 상태
        self.detail_at = None  # 상세 창을 연 시각. None 이면 닫혀 있다
        self.prev_key_pct = None  # 지난번 줄마다의 CPU%. 확 뛴 줄을 찾는다
        self.flashes = {}  # {줄 키: 번쩍이기 시작한 시각}
        self.last_table = {}  # {줄 키: (표 안 순서, 굴림 위치, 글자만 남긴 줄)} 지난번에 그린 표
        self.kill_watch = None  # 종료시킨 프로세스가 사라지는지 지켜본다. (PID, 생성 시각, 줄 키, 그만 볼 시각)
        self.vanish = None  # 사라지는 줄. (표 안 순서, 굴림 위치, 글자만 남긴 줄, 시작 시각)
        self._path_cache = (None, "")  # ((PID, 생성 시각), 실행 파일 경로)
        self.frozen = None  # 잠긴 동안의 줄 순서. {줄 키: 순번}
        self.locked_at = 0.0  # 잠근 시각. 테두리가 잠기는 연출에 쓴다
        self.row_text = {}  # {표 안 순서: 글자만 남긴 줄} 지난번에 그린 것. 바뀐 글자를 찾는다
        self.decoding = {}  # {표 안 순서: (바꿀 칸 목록, 시작 시각)} 해독되며 바뀌는 줄

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
        net = sample_network()

        # 전체 CPU 는 시스템 누적 시간으로 잰다. 프로세스를 더하는 방식은 인터럽트 처리
        # 시간을 놓치고, 재는 사이 끝난 프로세스 몫도 빠진다
        times = system_times()
        if times and self.prev_times:
            idle = times[0] - self.prev_times[0]
            busy_all = (times[1] - self.prev_times[1]) + (times[2] - self.prev_times[2])
            if busy_all > 0:
                self.total_cpu = max(0.0, min(100.0, (busy_all - idle) / busy_all * 100.0))
                self.cpu_hist.append(self.total_cpu)
                self.cpu_hist_at.append(now)
                self.ready = True
        self.prev_times = times

        # 코어별 사용률. 전체 CPU 가 낮아도 코어 하나가 꽉 차 있으면 그 프로그램은 느리다
        cores = core_times()
        if cores and len(cores) == len(self.prev_cores):
            pcts = []
            for (idle, total), (idle0, total0) in zip(cores, self.prev_cores):
                span = total - total0
                pcts.append(max(0.0, min(100.0, (span - (idle - idle0)) / span * 100.0)) if span > 0 else 0.0)
            self.core_pct = pcts
        self.prev_cores = cores

        rows = []
        compressed = 0
        elapsed = now - self.prev_t if self.prev_t else 0.0
        for pid, (born, cpu_s, private, ws, name, *_) in procs.items():
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

        # 전체 CPU 가 튀었는데 목록에 범인이 없을 때가 있다. 갱신 사이에 생겼다 끝난 짧은
        # 프로세스, 드라이버의 인터럽트 처리, 가상 머신 몫은 프로세스별 시간에 안 잡힌다
        if elapsed > 0:
            listed = sum(r[1] for r in rows)
            self.unlisted_cpu = max(0.0, self.total_cpu - listed)

        # 네트워크 속도. 어댑터를 새로 꽂았거나 재시작해서 수가 줄었으면 그 어댑터는 이번에 뺀다
        if elapsed > 0:
            down = up = 0
            for luid, (rx, tx, *_) in net.items():
                before = self.net_prev.get(luid)
                if before and rx >= before[0] and tx >= before[1]:
                    down += rx - before[0]
                    up += tx - before[1]
            self.net_rate = (down / elapsed, up / elapsed)
        self.net_prev = net
        self.net_links = [(n[4], n[2], n[3]) for n in net.values()]

        self.compressed = compressed
        self.rows = rows
        self.procs = procs  # 상세 창이 스레드·부모·시작 시각을 꺼내 쓴다
        self.prev = {pid: (p[0], p[1]) for pid, p in procs.items()}
        self.prev_t = now

        # 프로세스 CPU 가 확 뛴 줄은 CPU% 칸을 잠깐 번쩍였다가 식힌다. 시세판처럼 눈이 그리로 간다.
        # 첫 측정 직후는 모두 0 에서 뛴 것처럼 보여서 건너뛴다
        if elapsed > 0:
            current = {r[0]: r[1] for r in self.sorted_rows()}
            if self.prev_key_pct is not None:
                for key, pct in current.items():
                    before = self.prev_key_pct.get(key)
                    if before is not None and (pct - before) * NCPU >= FLASH_JUMP:
                        self.flashes[key] = now
            self.prev_key_pct = current
        self.flashes = {k: t for k, t in self.flashes.items() if now - t < FLASH_SECONDS}

        # 종료시킨 프로세스가 목록에서 사라졌으면 그 줄이 흩어지며 사라지는 연출을 건다
        if self.kill_watch:
            pid, born, key, until = self.kill_watch
            info = procs.get(pid)
            if info is None or info[0] != born:
                self.kill_watch = None
                seen = self.last_table.get(key)
                if seen:
                    self.vanish = (*seen, now)
            elif now > until:
                self.kill_watch = None

        # 화면 값이 따라갈 목표를 새로 건다
        tw = self.tween
        tw.set("cpu", self.total_cpu, now)
        for i, pct in enumerate(self.core_pct):
            tw.set(("core", i), pct, now)
        mem = self.mem
        tw.set("mem", mem["used"], now)
        tw.set("cache", mem["cache"], now)
        tw.set("commit", mem["commit"], now)
        tw.set("page", self.pagefile[0], now)
        if self.net_rate:
            tw.set("down", self.net_rate[0], now)
            tw.set("up", self.net_rate[1], now)

    def sorted_rows(self):
        """표에 그릴 줄. (키, CPU%, 메모리, 이름, 묶인 개수, 포트 목록, PID).

        키는 PID, 묶음 보기에서는 이름이다. 묶으면 CPU·메모리·포트를 합친다.
        PID 는 묶인 게 하나뿐일 때 그 프로세스의 것이다.
        """
        if self.grouped:
            groups = {}
            for pid, pct, private, name in self.rows:
                g = groups.setdefault(name, [name, 0.0, 0, name, 0, [], pid])
                g[1] += pct
                g[2] += private
                g[4] += 1
                g[5].extend(self.ports.get(pid, []))
            rows = [(*g[:5], sorted(set(g[5])), g[6]) for g in groups.values()]
        else:
            rows = [
                (pid, pct, private, name, 1, self.ports.get(pid, []), pid)
                for pid, pct, private, name in self.rows
            ]
        idx = 1 if self.sort_key == "cpu" else 2
        rows.sort(key=lambda r: r[idx], reverse=True)
        # 줄을 고르는 동안은 표가 잠긴다. 순서를 잠근 순간 그대로 두고 숫자만 새로 채운다.
        # 고르는 사이 순위가 바뀌어 줄이 위아래로 튀면 엉뚱한 걸 고르게 된다.
        # 잠근 뒤 새로 뜬 프로세스는 맨 아래에 붙고, 끝난 것은 빠진다
        if self.selected is None:
            self.frozen = None
            return rows
        if self.frozen is None:
            self.frozen = {r[0]: i for i, r in enumerate(rows)}
            self.locked_at = time.monotonic()
            return rows
        known = [r for r in rows if r[0] in self.frozen]
        known.sort(key=lambda r: self.frozen[r[0]])
        return known + [r for r in rows if r[0] not in self.frozen]

    @property
    def locked(self) -> bool:
        return self.selected is not None

    def toggle_group(self):
        """묶음 보기를 켜고 끈다. 고른 줄은 같은 프로세스(또는 그 묶음)로 옮겨 준다."""
        self.frozen = None  # 줄 키가 PID 와 이름 사이로 바뀌니 잠근 순서를 새로 잡는다
        if self.grouped:
            # 묶음에서 풀면 그 이름 중 지금 정렬 기준으로 가장 큰 것을 고른다
            name = self.selected
            self.grouped = False
            self.selected = next((r[0] for r in self.sorted_rows() if r[3] == name), None)
        else:
            name = next((r[3] for r in self.rows if r[0] == self.selected), None)
            self.grouped = True
            self.selected = name
        self.scroll = 0
        if self.selected is not None:
            self.move_selection(0)  # 고른 줄이 화면 안에 들게 굴린다
        if self.grouped:
            self.set_status("같은 이름의 프로세스를 한 줄로 합쳐 보는 중 (×N = 합친 개수) — g 로 하나씩 보기", CYAN)
        else:
            self.set_status("프로세스를 하나씩 보는 중 — g 로 같은 이름끼리 합치기", CYAN)

    def set_status(self, text: str, color: str = GRAY):
        self.status = (text, color, time.monotonic())

    def move_selection(self, step: int):
        rows = self.sorted_rows()
        if not rows:
            return
        keys = [r[0] for r in rows]
        if self.selected in keys:
            index = keys.index(self.selected) + step
        else:
            index = 0 if step >= 0 else len(keys) - 1
        index = max(0, min(len(keys) - 1, index))
        self.selected = keys[index]

        # 고른 줄이 화면 밖으로 나가면 따라 굴린다
        if index < self.scroll:
            self.scroll = index
        elif index >= self.scroll + self.visible_rows:
            self.scroll = index - self.visible_rows + 1

    def request_kill(self):
        """확인 단계로 넘긴다. 여기서 막을 건 미리 막는다."""
        if self.selected is None:
            self.set_status("종료할 프로세스를 ↑↓ 로 먼저 선택", YELLOW)
            return
        if self.grouped:
            # 하나뿐인 묶음은 그 프로세스를 끈다. 여럿 묶인 걸 통째로 끄면 같은 이름의
            # 딴 프로그램까지 휩쓸 수 있어서 풀고 하나씩 고르게 한다
            members = [r for r in self.rows if r[3] == self.selected]
            if len(members) > 1:
                self.set_status(
                    f"{self.selected} {len(members)}개를 합친 줄 — g 로 하나씩 보기로 바꾼 뒤 고르기", YELLOW
                )
                return
            target = members[0] if members else None
        else:
            target = next((r for r in self.rows if r[0] == self.selected), None)
        if target is None:
            self.set_status("종료할 프로세스를 ↑↓ 로 먼저 선택", YELLOW)
            return
        pid, name = target[0], target[3]
        if pid in PROTECTED_PIDS or name.lower() in PROTECTED_NAMES:
            self.set_status(f"{name} — Windows 핵심 프로세스라 종료 불가 (끄면 블루스크린·재시동)", RED)
            return
        if pid == os.getpid():
            self.set_status("wsc 자신은 여기서 종료 불가 — q 로 나가기", YELLOW)
            return
        born = self.prev.get(pid, (None,))[0]
        self.pending_kill = (pid, name, born)

    def do_kill(self, force: bool):
        pid, name, born = self.pending_kill
        self.pending_kill = None
        # 확인을 기다리는 사이 그 프로세스가 끝나고 같은 PID 로 딴 게 떴을 수 있다.
        # 그걸 엉뚱하게 죽이지 않도록 방금 읽은 목록으로 다시 맞춰본다
        fresh = sample_processes().get(pid)
        who = f"{name} (PID {pid})"
        if fresh is None or fresh[0] != born:
            self.set_status(f"{who} — 이미 종료됨", GRAY)
            self.needs_refresh = True
            return
        try:
            if force:
                terminate(pid)
                how = "강제 종료 완료"
            else:
                sent = close_windows(pid)
                if not sent:
                    self.set_status(
                        f"{who} — 닫을 창이 없는 프로세스. 끝내려면 k 다음 f (강제 종료)",
                        YELLOW,
                    )
                    return
                how = "창 닫기 요청 보냄. 저장 여부를 묻는 창이 떴을 수 있음"
        except ProcessLookupError:
            self.set_status(f"{who} — 이미 종료됨", GRAY)
        except PermissionError:
            self.set_status(
                f"{who} — 권한 부족. 관리자 권한 터미널에서 wsc 를 실행해야 종료 가능",
                RED,
            )
        except OSError as exc:
            self.set_status(f"{who} — 종료 실패 ({exc})", RED)
        else:
            self.set_status(f"{who} — {how}", GREEN)
            self.needs_refresh = True
            # 목록에서 사라지는 걸 보면 그 줄이 흩어지며 사라지게 그린다. 창 닫기는 저장 여부를
            # 묻느라 늦게 끝날 수 있어 몇 초 지켜본다
            row_key = name if self.grouped else pid
            self.kill_watch = (pid, born, row_key, time.monotonic() + 5.0)

    def window_signals(self) -> str:
        """창 제목과 작업 표시줄 아이콘에 띄울 제어 문자. 측정값이 바뀔 때만 다시 보낸다.

        제목에는 CPU·메모리를 적고, 작업 표시줄 아이콘에는 CPU% 를 진행 막대로 채운다.
        막대 색은 CPU 막대의 노랑·빨강 기준을 따른다. 창을 내려 둬도 아이콘만 보고 바쁜지 안다.
        """
        if not self.ready:
            return ""
        mem = self.mem
        mem_pct = mem["used"] / mem["total"] * 100.0 if mem["total"] else 0.0
        out = f"{ESC}]2;wsc · CPU {self.total_cpu:.0f}% · 메모리 {mem_pct:.0f}%{BEL}"
        if TASKBAR:
            # 상태 1 초록, 4 노랑(일시 정지 색), 2 빨강(오류 색). 0% 는 막대가 안 보여서 1 칸은 채운다
            frac = self.total_cpu / 100.0
            state = 2 if frac >= 0.85 else 4 if frac >= 0.60 else 1
            out += f"{ESC}]9;4;{state};{max(1, round(self.total_cpu))}{BEL}"
        return out

    def frame_wait(self, now: float):
        """연출 중이면 다음 장까지 기다릴 초. 움직이는 게 없으면 None (다음 갱신까지 쉰다)."""
        if (
            self.tween.busy(now)
            or self.vanish
            or (self.detail_at is not None and now - self.detail_at < DETAIL_OPEN_SECONDS)
            or any(now - t < FLASH_SECONDS for t in self.flashes.values())
            or self.decoding
            or (self.locked and now - self.locked_at < LOCK_SETTLE_SECONDS)
        ):
            return FRAME_SECONDS
        # 그래프는 늘 조금씩 흐른다. 상세 창 뒤에 깔려 어두울 때는 멈춰 둔다
        if self.graph_h and self.detail_at is None:
            return GRAPH_FRAME_SECONDS
        return None

    def open_detail(self):
        if self.selected is None:
            self.move_selection(0)  # 고른 줄이 없으면 맨 위 줄을 고른다
            if self.selected is None:
                return
        self.detail_at = time.monotonic()

    def detail_path(self, pid: int) -> str:
        """상세 창에 적을 실행 파일 경로. 창을 그릴 때마다 묻지 않게 PID·생성 시각으로 기억한다."""
        info = self.procs.get(pid)
        cache_key = (pid, info[0] if info else None)
        if self._path_cache[0] != cache_key:
            self._path_cache = (cache_key, process_path(pid))
        return self._path_cache[1]

    def detail_rows(self, row: tuple, inner_w: int, room: int) -> tuple:
        """상세 창의 (제목, 오른쪽 제목, 본문 줄 목록). 본문 한 줄은 [(글자, 글자색, 굵게)] 다.

        room 은 본문에 쓸 수 있는 줄 수다. 묶은 줄의 프로세스 목록은 이 안에 들어가는 만큼만 적는다.
        """
        key, pct, private, name, count, ports, pid = row
        label_w = 8
        value_w = inner_w - label_w
        now_wall = time.time()

        def field(label, value, note=""):
            value = dtrunc(value, value_w)
            parts = [(dpad(label, label_w), DETAIL_LABEL, False), (value, DETAIL_TEXT, False)]
            if note and dwidth(value) + 2 + dwidth(note) <= value_w:
                parts.append(("  " + note, DETAIL_DIM_TEXT, False))
            return parts

        def started(born):
            at = filetime_local(born)
            if at is None:
                return "알 수 없음", ""
            today = time.localtime(now_wall)[:3] == at[:3]
            stamp = time.strftime("오늘 %H:%M:%S" if today else "%m월 %d일 %H:%M", at)
            return stamp, human_age(now_wall - time.mktime(at))

        port_text = "  ".join(f":{p}" for p in ports) if ports else ""
        members = [r for r in self.rows if (r[3] == name if self.grouped else r[0] == pid)]
        sort_idx = 1 if self.sort_key == "cpu" else 2
        members.sort(key=lambda r: r[sort_idx], reverse=True)
        lead = members[0][0] if members else pid
        path = self.detail_path(lead) or "알 수 없음 (열어 볼 권한 없음)"
        body = [field("경로", mid_trunc(path, value_w))]

        if count <= 1:
            info = self.procs.get(pid)
            born, _, _, ws, _, threads, handles, parent = info if info else (0,) * 8
            stamp, age = started(born)
            body.append(field("시작", stamp, age))
            body.append(field("CPU", f"{pct:.1f}%", f"코어 하나의 {pct * NCPU:.0f}%"))
            body.append(field("메모리", human_bytes(private), f"작업 집합 {human_bytes(ws)}"))
            body.append(field("스레드", f"{threads:,}", f"핸들 {handles:,}"))
            # 부모가 먼저 끝나면 그 PID 를 딴 프로세스가 물려받을 수 있다. 자식보다 늦게 생긴 건 부모가 아니다
            dad = self.procs.get(parent)
            if parent and dad and dad[0] <= born:
                body.append(field("부모", dad[4], f"PID {parent}"))
            elif parent:
                body.append(field("부모", "이미 끝남", f"PID {parent}"))
            body.append(field("포트", port_text or "없음"))
            return name, f"PID {pid}", body

        threads = sum(self.procs.get(r[0], (0,) * 8)[5] for r in members)
        body.append(field("합계", f"CPU {pct:.1f}%  메모리 {human_bytes(private)}", f"스레드 {threads:,}"))
        body.append(field("포트", port_text or "없음"))
        body.append([])
        body.append([(f"{'PID':>7}  {'CPU%':>6}  {rpad('메모리', 8)}  시작", DETAIL_LABEL, False)])
        # 남은 줄에 들어가는 만큼만. 넘치면 마지막 줄을 '외 N개' 로 쓴다
        fit = max(1, room - len(body))
        shown = members if len(members) <= fit else members[:fit - 1]
        for m_pid, m_pct, m_private, _ in shown:
            stamp, age = started(self.procs.get(m_pid, (0,))[0])
            body.append([
                (f"{m_pid:>7}  {m_pct:>6.1f}  {human_bytes(m_private):>8}  ", DETAIL_TEXT, False),
                (dtrunc(f"{stamp}  {age}", max(1, inner_w - 29)), DETAIL_DIM_TEXT, False),
            ])
        if len(shown) < len(members):
            body.append([(f"{'':>7}  외 {len(members) - len(shown)}개", DETAIL_DIM_TEXT, False)])
        return f"{name} ×{count}", f"프로세스 {count}개", body

    def overlay_detail(self, out: list, cols: int, lines: int) -> list:
        """상세 창을 화면 위에 얹는다. 뒤 화면은 어둡게 다시 칠하고 창 오른쪽·아래에 그림자를 깐다.

        여는 동안(DETAIL_OPEN_SECONDS) 뒤 화면이 서서히 어두워지고 창이 가운데에서 좌우로 펼쳐진다.
        """
        row = next((r for r in self.sorted_rows() if r[0] == self.selected), None)
        if row is None:
            self.detail_at = None
            self.set_status("프로세스가 끝나서 상세 창을 닫음", GRAY)
            return out
        grow = ease_out((time.monotonic() - self.detail_at) / DETAIL_OPEN_SECONDS)

        box_w = max(30, min(cols - 4, 80))
        inner_w = box_w - 4  # 양쪽 테두리와 한 칸씩 띄운 자리
        # 위아래 테두리, 본문 뒤 빈 줄과 조작 줄을 뺀 자리. 창이 화면을 다 덮으면 뒤가 안 보여 모달 같지 않다
        room = max(3, min(DETAIL_MAX_BODY, lines - 2 - 4 - 4))
        title, right_title, body = self.detail_rows(row, inner_w, room)
        body = body[:room]
        keys = [("Esc", "닫기"), ("↑↓", "다른 줄")]
        keys.append(("g", "하나씩 보기") if row[4] > 1 else ("k", "종료"))
        footer = []
        for k, label in keys:
            footer.append((f" {k} ", (24, 24, 28), True, DETAIL_KEY))
            footer.append((f" {label}   ", DETAIL_LABEL, False, None))
        rows_out = [None] + body + [[], footer] + [None]  # None 은 위아래 테두리
        box_h = len(rows_out)

        # 뒤 화면을 칸으로 풀어 어둡게 칠한다
        grid = [to_cells(line, cols) for line in out[:lines]]
        while len(grid) < lines:
            grid.append(to_cells("", cols))
        dim = 1 - (1 - DETAIL_DIM) * grow
        for cells in grid:
            for cell in cells:
                cell[1] = darken(cell[1], dim)

        # 펼쳐지는 동안의 폭. 가운데를 기준으로 좌우가 같이 늘어난다
        cur_w = max(8, round(box_w * (0.4 + 0.6 * grow)))
        cur_inner = cur_w - 4
        top = max(0, (lines - box_h) // 2)
        left = max(0, (cols - cur_w) // 2)

        # 그림자. 오른쪽으로 두 칸, 아래로 한 줄. 칸은 세로로 길어서 두 칸이라야 두께가 맞아 보인다
        shade = DETAIL_SHADOW / DETAIL_DIM
        for r in range(top + 1, min(lines, top + box_h + 1)):
            span = range(left + cur_w, left + cur_w + 2) if r < top + box_h else range(left + 2, left + cur_w + 2)
            for c in span:
                if c < cols:
                    grid[r][c][1] = darken(grid[r][c][1], shade)

        ascii_box = USE_ASCII
        h, v = ("-", "|") if ascii_box else ("─", "│")
        corners = ("+", "+", "+", "+") if ascii_box else ("╭", "╮", "╰", "╯")
        border = (DETAIL_BORDER, DETAIL_BG, False)
        fill = (DETAIL_TEXT, DETAIL_BG, False)
        for i, parts in enumerate(rows_out):
            r = top + i
            if r >= lines:
                break
            cells = grid[r]
            if parts is None:
                first = i == 0
                put_text(cells, left, (corners[0] if first else corners[2]) + h * (cur_w - 2)
                         + (corners[1] if first else corners[3]), border)
                if first and cur_inner > 8:
                    # 위 테두리에 제목을 박는다. 왼쪽은 이름, 오른쪽은 PID·개수
                    name = dtrunc(title, max(4, cur_inner - dwidth(right_title) - 4))
                    put_text(cells, left + 2, f" {name} ", (DETAIL_TITLE, DETAIL_BG, True))
                    if dwidth(name) + dwidth(right_title) + 6 <= cur_inner:
                        put_text(cells, left + cur_w - 3 - dwidth(right_title),
                                 f" {right_title} ", (DETAIL_LABEL, DETAIL_BG, False))
                continue
            put_text(cells, left, v, border)
            put_text(cells, left + 1, " " * (cur_w - 2), fill)
            put_text(cells, left + cur_w - 1, v, border)
            col, room_w = left + 2, cur_inner
            for part in parts:
                if room_w <= 0:
                    break
                text, fg, bold = part[:3]
                bg = part[3] if len(part) > 3 and part[3] else DETAIL_BG
                text = dtrunc(text, room_w) if dwidth(text) > room_w else text
                if not text:
                    break
                put_text(cells, col, text, (fg, bg, bold))
                col += dwidth(text)
                room_w -= dwidth(text)
        return [from_cells(cells) for cells in grid]

    def render(self, cols: int, lines: int) -> list:
        out = self.render_main(cols, lines)
        if self.detail_at is not None:
            out = self.overlay_detail(out, max(52, cols), lines)
        return out

    def render_main(self, cols: int, lines: int) -> list:
        cols = max(52, cols)
        mem = self.mem
        page_used, page_total = self.pagefile
        pressure_text, pressure_color, pressure_note = memory_pressure(mem)

        bar_w = max(12, min(28, cols - 50))
        label_w = 9  # '네트워크' 가 8칸이다
        out = []

        # 막대와 숫자는 측정값을 따라 미끄러지는 값으로 그린다. 경고·색 기준은 실제 측정값으로 본다.
        # 한창 옮겨 가는 중간값으로 경고를 띄웠다 거뒀다 하면 깜빡인다
        now = time.monotonic()

        def shown(name, actual):
            return self.tween.get(name, now, actual)

        cpu_now = shown("cpu", self.total_cpu)
        mem_used = shown("mem", mem["used"])
        mem_cache = shown("cache", mem["cache"])
        commit_used = shown("commit", mem["commit"])
        page_shown = shown("page", page_used)
        net_shown = None
        if self.net_rate:
            net_shown = (shown("down", self.net_rate[0]), shown("up", self.net_rate[1]))
        # 창이 넉넉히 높으면 CPU 추이를 점자 그래프로 크게 그린다. 그때는 CPU 줄 끝의 작은 추이를 뺀다
        graph_h = 0
        if self.live and not USE_ASCII:
            graph_h = next((h for at_least, h in GRAPH_HEIGHTS if lines >= at_least), 0)

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
        # 메모리 압박은 제목 줄의 색 배지로. 평소엔 한 칸짜리 줄을 따로 차지할 만한 정보가 아니다
        pressure = f" 메모리 {pressure_text} "
        right = f"{admin}{pressure}  {clock}  갱신 {rate} "
        name = f" wsc {VERSION}  "
        brand_w = cols - dwidth(name) - dwidth(right) - 2
        brand = dtrunc(CPU_BRAND, brand_w) if brand_w >= 6 else ""
        pad = max(1, cols - dwidth(name) - dwidth(brand) - dwidth(right))
        admin_cell = f"{YELLOW}{BOLD}{admin}{RESET}{HEADER_BG}" if admin else ""
        badge = f"{PRESSURE_BADGE[pressure_text]}{BOLD}{pressure}{RESET}{HEADER_BG}"
        out.append(
            f"{HEADER_BG}{LOGO_ON_HEADER} wsc {GRAY_ON_HEADER}{VERSION}  {RESET}{HEADER_BG}{brand}"
            f"{' ' * pad}{admin_cell}{badge}  {BOLD}{clock}{RESET}{HEADER_BG}  "
            f"{GRAY_ON_HEADER}갱신 {rate_color}{rate} {RESET}"
        )
        out.append("")

        # 값 칸은 '쓰는 양 / 전체' 두 칸으로 나눠 폭을 고정한다. 앞 숫자끼리 오른쪽 끝이 맞고,
        # 뒤의 회색 정보도 한 세로줄에 선다. 자릿수가 바뀔 때마다 줄이 들썩이지도 않는다
        values = {
            "cpu": (f"{cpu_now:.1f}%" if self.ready else "측정 중", ""),
            "mem": (human_bytes(mem_used), human_bytes(mem["total"])),
            "commit": (human_bytes(commit_used), human_bytes(mem["commit_limit"])),
            "page": (
                (human_bytes(page_shown), human_bytes(page_total)) if page_total else ("꺼 둠", "")
            ),
        }
        if not self.net_links:
            values["net"] = ("연결 없음", "")
        elif self.net_rate is None:
            values["net"] = ("측정 중", "")
        else:
            # 영문 기호 모드에서 화살표를 v ^ 로 바꾸면 무슨 뜻인지 안 읽혀서 낱말로 적는다
            down, up = ("in ", "out ") if USE_ASCII else ("↓", "↑")
            values["net"] = (
                f"{down}{human_rate(net_shown[0])}", f"{up}{human_rate(net_shown[1])}"
            )
        # 네트워크 속도는 늘 자릿수가 바뀐다. 가장 긴 모양(↓12.3MB/s)에 맞춰 폭을 고정해 둔다
        left_w = max(9, *(dwidth(v[0]) for v in values.values()))
        right_w = max(9, *(dwidth(v[1]) for v in values.values()))
        head_w = 1 + label_w + bar_w + 2 + left_w + 3 + right_w

        def summary(label, frac, key, extras, color="", reserve=0, sep=" / ", extra=0.0,
                    bar=None, value_colors=("", "")):
            used_text, total_text = values[key]
            total_cell = f"{sep}{dpad(total_text, right_w)}" if total_text else " " * (3 + right_w)
            tail, used = fit_extras(head_w + reserve, extras, cols)
            if bar is None:
                bar = draw_bar(frac, bar_w, color, extra)
            line = (
                f" {dpad(label, label_w)}{bar}  "
                f"{BOLD}{value_colors[0]}{rpad(used_text, left_w)}{RESET}"
                f"{BOLD}{value_colors[1]}{total_cell}{RESET}{tail}"
            )
            return line, used - reserve

        # CPU — 윈도우에는 부하 평균이 없어서 그 자리에 프로세스·스레드 수를 둔다.
        # 끝에는 최근 추이를 붙인다. 방금 튄 건지 계속 높은 건지가 한눈에 갈린다.
        # 추이 자리를 먼저 떼어 두고, 남는 폭에 회색 정보를 순위대로 채운다
        spark_room = 2 + 12 if len(self.cpu_hist) >= 2 and not graph_h else 0
        cpu_extras = [
            (f"{NCPU}코어", GRAY, 3),
            (f"프로세스 {mem['processes']}", GRAY, 2),
            (f"스레드 {mem['threads']}", GRAY, 1),
        ]
        # 표의 프로세스로 설명 안 되는 몫이 크면 맨 앞에 경고로 둔다. 표를 뒤져도 범인이 없는 이유다.
        # 숫자만 띄우면 무슨 뜻인지 모르니, 자리가 있으면 흔한 원인을 회색으로 붙인다.
        # 좁아서 경고·원인과 추이를 다 못 넣으면 추이를 접는다. 이건 표를 봐서는 대신 알 길이 없다.
        # 숫자를 앞에 둔다. 좁은 창에서 끝이 잘려도 몇 % 인지는 남게
        if self.ready and self.unlisted_cpu >= UNLISTED_WARN:
            warn = f"{self.unlisted_cpu:.0f}%는 표에 없음"
            hint = "(잠깐 뜬 프로세스·드라이버·VM 몫)"
            cpu_extras.insert(0, (warn, YELLOW, None))
            cpu_extras.insert(1, (hint, GRAY, 4))
            with_warn = head_w + 2 + dwidth(warn)
            with_hint = with_warn + 2 + dwidth(hint)
            # 추이를 접어서 원인까지 들어갈 때만 접는다. 접어도 안 들어가면 추이를 남긴다
            if with_hint + spark_room > cols >= with_hint or with_warn + spark_room > cols:
                spark_room = 0
        line, used = summary(
            "CPU", cpu_now / 100.0, "cpu", cpu_extras, reserve=spark_room,
        )
        spark_w = min(SPARK_LEN, cols - used - 2)
        if spark_room and spark_w >= 8:
            line += f"  {draw_spark(self.cpu_hist, spark_w)}"
        out.append(line)

        # 코어별 — 전체 CPU 가 낮은데 느리면 코어 하나가 꽉 찬 경우가 많다 (한 스레드로만 도는
        # 프로그램, 무한 루프). 평균에 묻히는 걸 한 칸씩 펼쳐 보인다. 막대와 같은 세로줄에서 시작한다
        if self.core_pct:
            # 막대부터 값 칸 끝까지를 쓴다. 설명 글은 붙이지 않는다. 코어 하나가 잠깐씩 꽉 차는 건
            # 흔해서, 글로 띄우면 수시로 깜빡이는 경고가 되고 정작 볼 건 칸 높이로 충분히 보인다
            cores = [shown(("core", i), pct) for i, pct in enumerate(self.core_pct)]
            strip = draw_cores(cores, head_w - 1 - label_w)
            out.append(f" {dpad('코어', label_w)}{strip}")
        else:
            out.append(f" {dpad('코어', label_w)}{DIM}측정 중{RESET}")

        # 메모리. 좁으면 캐시부터 뺀다. 압축이 쌓이는 건 부족 신호라 더 오래 남긴다.
        # 막대는 사용 중 뒤에 캐시를 흐린 파랑으로 잇는다. 캐시는 필요하면 바로 내주는 몫이라
        # 막대가 길어 보여도 파란 데까지는 여유다. 옆의 '캐시' 글자를 같은 색으로 칠해 범례로 쓴다.
        # 압박이 주의·위험이면 무엇이 넘었는지와 할 일을 맨 앞에 경고로 둔다. 배지는 제목 줄에 있다
        mem_frac = mem_used / mem["total"] if mem["total"] else 0.0
        # 캐시는 대부분 '사용 가능' 안에 들어 있다. 남은 자리보다 크게는 못 그린다
        cache_frac = min(mem_cache, mem["total"] - mem_used) / mem["total"] if mem["total"] else 0.0
        mem_extras = [
            (f"압축 {human_bytes(self.compressed)}", GRAY, 2),
            (f"캐시 {human_bytes(mem['cache'])}", CACHE_COLOR, 1),
        ]
        if pressure_note:
            mem_extras.insert(0, (pressure_note, pressure_color, None))
        out.append(summary("메모리", mem_frac, "mem", mem_extras, extra=cache_frac)[0])

        # 커밋 — 프로그램들이 '쓰겠다'고 받아간 메모리 총량. 한계에 닿으면 새 할당이 실패한다
        commit_frac = mem["commit"] / mem["commit_limit"] if mem["commit_limit"] else 0.0
        commit_note = []
        # 비율보다 '얼마 남았나' 가 와닿는다
        commit_left = human_bytes(max(0, mem["commit_limit"] - mem["commit"]))
        if commit_frac >= 0.90:
            commit_note = [
                (f"한계까지 {commit_left} — 새 프로그램 실행이 실패할 수 있음", f"{RED}{BOLD}", None)
            ]
        elif commit_frac >= 0.80:
            commit_note = [(f"한계까지 {commit_left} 남음", YELLOW, None)]
        commit_bar = commit_used / mem["commit_limit"] if mem["commit_limit"] else 0.0
        out.append(summary("커밋", commit_bar, "commit", commit_note)[0])

        # 페이지 파일 — 맥의 스왑. 비율보다 절대량이 중요해서 색도 양으로 정한다
        page_note = []
        page_color = GREEN
        if page_used >= 3 * 1024**3:
            page_color = RED
            page_note = [("버벅임 주원인 — 메모리가 디스크로 많이 밀려남", f"{RED}{BOLD}", None)]
        elif page_used >= 1024**3:
            page_color = YELLOW
            page_note = [("메모리 부족 조짐 — 디스크로 밀려나기 시작", YELLOW, None)]
        page_frac = page_shown / page_total if page_total else 0.0
        out.append(summary("페이지", page_frac, "page", page_note, page_color)[0])

        # 네트워크 — 막대를 반으로 갈라 왼쪽은 받기(↓), 오른쪽은 보내기(↑). 한 막대에 둘 중
        # 큰 쪽만 그리면 어느 방향인지 알 길이 없다. 옆의 속도 글자도 같은 색으로 칠해 짝을 맞춘다.
        # 프로세스별 사용량은 윈도우가 관리자 권한 없이는 알려주지 않아서 전체만 보인다
        net_frac = 0.0
        net_extras = []
        rx_frac = tx_frac = 0.0
        if self.net_links:
            rx_link = sum(link[1] for link in self.net_links)
            tx_link = sum(link[2] for link in self.net_links)
            if self.net_rate:
                down, up = self.net_rate
                net_frac = max(
                    down * 8 / rx_link if rx_link else 0.0,
                    up * 8 / tx_link if tx_link else 0.0,
                )
                rx_frac = log_frac(net_shown[0], rx_link / 8)
                tx_frac = log_frac(net_shown[1], tx_link / 8)
            if net_frac >= 0.85:
                net_extras.append(("회선이 거의 가득 참 — 내려받기·화상회의가 느려질 수 있음", YELLOW, None))
            first = self.net_links[0]
            name = first[0] if len(self.net_links) == 1 else f"{first[0]} 외 {len(self.net_links) - 1}"
            net_extras.append((name, GRAY, 1))
            net_extras.append((f"회선 {human_bps(max(rx_link, tx_link))}", GRAY, 2))
        if USE_ASCII:
            # 화살표가 v ^ 로 바뀌면 안 읽혀서 뺀다. 방향은 옆의 in·out 글자로 안다
            half = (bar_w - 1) // 2
            net_bar = f"{draw_bar(rx_frac, half, NET_DOWN)} {draw_bar(tx_frac, bar_w - 1 - half, NET_UP)}"
        else:
            half = (bar_w - 3) // 2
            net_bar = (
                f"{NET_DOWN}↓{draw_bar(rx_frac, half, NET_DOWN)} "
                f"{NET_UP}↑{draw_bar(tx_frac, bar_w - 3 - half, NET_UP)}"
            )
        out.append(summary(
            "네트워크", net_frac, "net", net_extras, sep="   ",
            bar=net_bar, value_colors=(NET_DOWN, NET_UP),
        )[0])

        # CPU 추이 그래프. 막대와 같은 세로줄에서 시작해 창 오른쪽 끝까지 쓴다.
        # 갱신 때마다 한 칸씩 툭 밀면 모든 칸의 점 모양이 한꺼번에 바뀌어 덜컥거린다.
        # 그래서 시각에 맞춰 그린다. 측정값 사이를 이어 그리고, 그사이 흐른 시간만큼 조금씩 민다
        self.graph_h = graph_h
        if graph_h:
            graph_w = cols - 1 - label_w
            keep = graph_w * 2 // GRAPH_DOTS_PER_SAMPLE + 2
            points = graph_points(
                list(self.cpu_hist)[-keep:], list(self.cpu_hist_at)[-keep:], now, graph_w * 2
            )
            # 이름표는 달지 않는다. CPU 줄 바로 아래 같은 세로줄에 서 있어 무슨 그래프인지는 자리로 안다
            for row in draw_graph(points, graph_w, graph_h):
                out.append(f" {' ' * label_w}{row}")
        # 기기 전체 상태와 프로세스 표를 가르는 줄. 표가 잠기면 잠금 테두리의 윗변이 된다. 표를 다 그린 뒤 채운다
        sep_at = len(out)
        out.append("")

        # 프로세스 표
        # 포트 칸은 자리가 있을 때만 낸다. 좁은 창에서는 이름이 먼저다
        port_w = 9 if cols >= 76 else 0
        # 이름 칸이 창 끝까지 간다. 제목 줄·조작 줄과 오른쪽 끝이 맞아야 표가 반듯해 보인다.
        # 양 끝 한 칸씩은 잠금 테두리 자리로 늘 비워 둔다. 잠글 때마다 표가 들썩이지 않게
        table_w = cols - 2
        name_w = max(14, table_w - 29 - (port_w + 2 if port_w else 0))
        # 색 코드는 폭 계산 뒤에 감싼다. 안 그러면 이스케이프 문자까지 폭으로 세서 표가 어긋난다
        # 정렬 기준 칸에는 ▼ 를 붙인다. 굵은 글씨만으로는 어느 쪽인지 잘 안 보인다
        cpu_hdr = rpad("CPU%▼" if self.sort_key == "cpu" else "CPU%", 7)
        mem_hdr = rpad("메모리▼" if self.sort_key == "mem" else "메모리", 8)
        if self.sort_key == "cpu":
            cpu_hdr = f"{BOLD}{cpu_hdr}{RESET}{HEADER_BG}"
        else:
            mem_hdr = f"{BOLD}{mem_hdr}{RESET}{HEADER_BG}"
        port_hdr = f"{dpad('포트', port_w)}  " if port_w else ""
        # 합쳐 보는 중이면 이름 칸 머리에 그 뜻을 적는다. ×27 만 보고는 무슨 숫자인지 모른다
        name_hdr = dpad("이름", name_w)
        if self.grouped:
            hint = dtrunc("같은 이름끼리 합침 · ×N = 합친 개수", max(0, name_w - 6))
            if name_w - 6 >= 10:
                name_hdr = f"이름  {GRAY_ON_HEADER}{dpad(hint, name_w - 6)}"
        out.append(
            f"{HEADER_BG} {rpad('PID', 7)}  {cpu_hdr}  {mem_hdr}  "
            f"{port_hdr}{name_hdr}{RESET}"
        )

        used_lines = len(out) + 2  # 표 아래 상태 줄과 도움말 줄 확보
        limit = max(3, lines - used_lines)
        self.visible_rows = limit

        rows = self.sorted_rows()
        # 고른 줄이 목록 밖으로 나가지 않게 굴림 위치를 다듬는다
        self.scroll = max(0, min(self.scroll, max(0, len(rows) - limit)))
        # 종료시킨 줄이 흩어지는 중이면 그 자리를 비워 두고 거기에 연출을 그린다.
        # 다 흩어지면 비운 자리가 없어지면서 아래 줄들이 한 칸씩 올라와 메운다
        vanish = None
        if self.vanish:
            v_idx, v_scroll, v_text, v_at = self.vanish
            if now - v_at >= VANISH_SECONDS:
                self.vanish = None
            elif v_scroll == self.scroll and v_idx < limit:
                vanish = (v_idx, v_text, now - v_at)
        window = rows[self.scroll : self.scroll + limit - (1 if vanish else 0)]
        entries = list(window)
        if vanish:
            entries.insert(min(vanish[0], len(entries)), None)

        # 몇 번째를 보고 있는지 알리는 꼬리표. 마지막 줄에 그냥 붙이면 줄이 창 폭을
        # 넘어 다음 줄로 접히고, 그만큼 화면이 밀려 올라간다. 그래서 그 줄만
        # 이름 칸을 미리 좁혀 자리를 만들어 둔다
        count_note = ""
        if len(rows) > limit:
            shown = f"{self.scroll + 1}–{min(self.scroll + limit, len(rows))}"
            count_note = f" {shown}/{len(rows)}"

        # 갱신으로 바뀐 글자는 무작위 글자로 깜빡이다 굳게 그린다 (해독 연출). 잠긴 동안은 멈춘다.
        # 글자가 바뀐 칸만 건드려서, 숫자 몇 자리만 바뀐 줄은 그 자리만 깜빡인다
        decode_on = self.tween.enabled and not self.locked
        if not decode_on:
            self.decoding.clear()
        row_text = {}
        table = {}
        for idx, entry in enumerate(entries):
            last_row = idx == len(entries) - 1
            note = f"{GRAY}{count_note}{RESET}" if last_row and count_note else ""
            if entry is None:
                out.append(vanish_line(vanish[1], vanish[2]) + note)
                continue
            key, pct, private, name, count, ports, pid = entry
            col_w = max(6, name_w - dwidth(count_note)) if last_row else name_w
            chosen = key == self.selected
            port_text = format_ports(ports) if port_w else ""
            name_cell = dpad(name, col_w)
            # 여럿 묶인 줄은 PID 자리에 몇 개를 합쳤는지 적는다. 하나뿐이면 그 PID 를 그대로 둔다
            first = f"×{count}" if count > 1 else str(pid)
            port_plain = f"{dpad(port_text, port_w)}  " if port_w else ""
            body = f"{first:>7}  {pct:>7.1f}  {human_bytes(private):>8}  {port_plain}{name_cell}"
            # 글자만 남긴 줄을 기억해 둔다. 이 줄을 종료시키면 이걸 부숴 가며 사라지게 그린다
            table[key] = (idx, self.scroll, f" {body}")
            if chosen:
                # 고른 줄은 색을 다 빼고 흰 글씨 하나로. 파란 바탕 위 색 글자는 안 읽힌다
                line = f"{SELECT_BG}{BOLD}›{body}{RESET}"
            else:
                port_cell = ""
                if port_w:
                    port_color = CYAN if port_text else DIM
                    port_cell = f"{port_color}{dpad(port_text, port_w)}{RESET}  "
                mem_color = proc_mem_color(private, mem["total"])
                first_color = CYAN if count > 1 else ""  # 합친 줄이 눈에 걸리게
                cpu_cell = f"  {proc_cpu_color(pct)}{pct:>7.1f}{RESET}  "
                flash_at = self.flashes.get(key)
                if flash_at is not None and now - flash_at < FLASH_SECONDS:
                    # 바탕을 밝혔다가 식힌다. 밝을 땐 글자를 검게 해야 읽힌다. 칸 앞뒤 한 칸씩 같이 칠한다
                    heat = (1 - (now - flash_at) / FLASH_SECONDS) ** 1.6
                    bg = ";".join(str(round(c * heat)) for c in FLASH_RGB)
                    fg = f"{ESC}[38;2;20;20;20m" if heat > 0.45 else proc_cpu_color(pct)
                    cpu_cell = f" {ESC}[48;2;{bg}m{fg}{BOLD} {pct:>7.1f} {RESET} "
                line = (
                    f" {first_color}{first:>7}{RESET}{cpu_cell}"
                    f"{mem_color}{human_bytes(private):>8}{RESET}  "
                    f"{port_cell}{dim_ext(name_cell)}"
                )
            line += note
            plain = f" {body}"
            row_text[idx] = plain
            before = self.row_text.get(idx, "")
            if decode_on and before[1:] != plain[1:]:
                self.decoding[idx] = (decode_spots(before, plain, table_w), now)
            spell = self.decoding.get(idx)
            if spell:
                progress = (now - spell[1]) / LIST_DECODE_SECONDS
                if progress >= 1.0:
                    del self.decoding[idx]
                else:
                    line = decode_line(line, spell[0], progress, table_w)
            out.append(line)
        self.last_table = table
        self.row_text = row_text
        for idx in [i for i in self.decoding if i not in row_text]:
            del self.decoding[idx]

        # 잠금 테두리. 표 머리부터 마지막 줄까지 양옆에 세로줄을 두르고, 가르는 줄을 윗변으로 쓴다.
        # 잠기는 순간 하얗게 번쩍였다가 호박색으로 가라앉는다. 안 잠겼으면 양옆은 빈칸이다
        if self.locked:
            settle = ease_out((now - self.locked_at) / LOCK_SETTLE_SECONDS)
            lock_rgb = tuple(round(255 + (c - 255) * settle) for c in LOCK_RGB)
            frame = rgb(lock_rgb)
            if USE_ASCII:
                corner_l, corner_r, side, edge, title = "+", "+", "|", "-", " LOCK "
            else:
                corner_l, corner_r, side, edge, title = "╭", "╮", "│", "─", " 🔒 잠김 "
            hint = " 순서 고정 · Esc 로 풀기 "
            if dwidth(title) + dwidth(hint) + 4 > cols:
                hint = ""
            rest = max(0, cols - 3 - dwidth(title) - dwidth(hint))
            out[sep_at] = (
                f"{frame}{corner_l}{edge}{BOLD}{title}{RESET}{GRAY}{hint}{RESET}"
                f"{frame}{edge * rest}{corner_r}{RESET}"
            )
            left_side = right_side = f"{frame}{side}{RESET}"
        else:
            out[sep_at] = f"{DIM}{'─' * cols}{RESET}"
            left_side = right_side = " "
        for i in range(sep_at + 1, len(out)):
            out[i] = f"{left_side}{out[i]}{right_side}"

        # 알림 줄. 없으면 빈 줄로 남겨 아래 도움말 위치가 흔들리지 않게 한다.
        # 표가 잠겨 있으면 잠금 테두리의 아랫변이 되고, 알릴 말은 그 선 안에 박는다
        text, color, shown_at = self.status
        if text and time.monotonic() - shown_at < 5.0:
            message = (text, color)
        elif self.update_ready:
            # 알릴 말이 없을 때만. 조작 줄에 끼워 넣으면 '누를 것'과 섞여 헷갈린다
            message = (f"새 버전 {self.latest_version} 나옴 — q 로 나간 뒤 wsc --update", f"{CYAN}{BOLD}")
        else:
            message = None
        if self.locked:
            corner_l, corner_r, edge = ("+", "+", "-") if USE_ASCII else ("╰", "╯", "─")
            inner = ""
            if message:
                inner = f" {dtrunc(message[0], cols - 6)} "
            rest = max(0, cols - 3 - dwidth(inner))
            out.append(
                f"{frame}{corner_l}{edge}{RESET}{message[1] if message else ''}{inner}{RESET}"
                f"{frame}{edge * rest}{corner_r}{RESET}"
            )
        elif message:
            out.append(f"{message[1]} {dtrunc(message[0], cols - 2)}{RESET}")
        else:
            out.append("")

        if self.pending_kill:
            pid, name, _ = self.pending_kill
            keys, keys_w = "", 0
            for key, label in (("y", "창 닫기"), ("f", "강제"), ("n", "취소")):
                keys += f"{KEY_BG}{BOLD} {key} {RESET}{DANGER_BG}{BOLD} {label}  "
                keys_w += dwidth(key) + dwidth(label) + 5
            question = f" 종료 확인: {dtrunc(name, max(10, cols - keys_w - 24))} (PID {pid})"
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
            ("Enter", "자세히", "상세", False, False),
            ("k", "종료시키기", "종료", False, False),
            ("c", "CPU순", "CPU", False, self.sort_key == "cpu"),
            ("m", "메모리순", "메모리", False, self.sort_key == "mem"),
            # 지금 상태가 아니라 누르면 무엇이 되는지를 적는다
            ("g", "하나씩 보기" if self.grouped else "같은 이름 합치기",
             "펼치기" if self.grouped else "합치기", False, False),
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
                self.set_status(f"{name} (PID {pid}) 종료 취소", GRAY)
            return True

        # 상세 창이 떠 있으면 닫기·종료·줄 옮기기만 받는다. q 는 나가지 않고 창만 닫는다.
        # 줄을 옮기면 창은 새로 고른 줄을 따라간다
        moves = ("UP", "DOWN", "PGUP", "PGDN", "HOME", "END")
        if self.detail_at is not None and key not in moves:
            if key in ("\x03", "\x04"):
                return False
            if key in ("ESC", "\r", "q", "Q"):
                self.detail_at = None
            elif key in ("k", "K"):
                self.detail_at = None
                self.request_kill()
            elif key in ("g", "G"):
                self.toggle_group()
            return True

        if key in ("q", "Q", "\x03", "\x04"):
            return False
        if key == "\r":
            self.open_detail()
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
            self.selected = None
        elif key in ("g", "G"):
            self.toggle_group()
        elif key in ("c", "C"):
            self.sort_key = "cpu"
            self.frozen = None  # 정렬을 바꾸라는 건 순서를 새로 잡으라는 뜻이다. 잠겨 있어도 다시 줄 세운다
        elif key in ("m", "M"):
            self.sort_key = "mem"
            self.frozen = None
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


def on_pseudo_console() -> bool:
    """의사 콘솔(ConPTY) 위에서 도는가. Windows Terminal·VS Code 같은 요즘 터미널이 이렇다.

    그런 터미널은 콘솔 창 대신 'PseudoConsoleWindow' 라는 숨은 창을 둔다.
    옛 콘솔 창이면 'ConsoleWindowClass' 다.
    """
    hwnd = kernel32.GetConsoleWindow()
    if not hwnd:
        return False
    name = ctypes.create_unicode_buffer(64)
    user32.GetClassNameW(hwnd, name, len(name))
    return name.value == "PseudoConsoleWindow"


def wants_ascii() -> bool:
    """옛 콘솔을 한중일 코드 페이지로 쓰는 중이면 영문 기호로 그린다.

    Windows Terminal(WT_SESSION)이나 VS Code 같은 터미널(TERM_PROGRAM)은
    폭이 애매한 글자를 한 칸으로 그려서 괜찮다. 윈도우 11 은 시작 메뉴에서 연
    PowerShell 도 Windows Terminal 로 넘겨 띄우는데, 그렇게 넘겨받은 창에는
    WT_SESSION 이 없어서 콘솔 창 종류로 한 번 더 가린다.
    """
    if os.environ.get("WT_SESSION") or os.environ.get("TERM_PROGRAM"):
        return False
    if on_pseudo_console():
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
    sys.stdout.write(SYNC_ON + frame + SYNC_OFF)
    sys.stdout.flush()


def render_splash(monitor: Monitor, cols: int, rows: int, progress: float) -> list:
    """시작 화면. 로고 아래에 기기 이름과 첫 측정이 얼마나 됐는지를 띄운다.

    로고는 처음 LOGO_DECODE_SECONDS 동안 무작위 글자에서 제 글자로 '해독' 되며 나타난다.
    """
    elapsed = progress * SPLASH_SECONDS
    logo, logo_w = logo_lines(elapsed / LOGO_DECODE_SECONDS)
    left = " " * max(1, (cols - logo_w) // 2)
    specs = f"{CPU_BRAND} · {NCPU}코어 · 메모리 {human_bytes(monitor.mem['total'])}"
    body = [
        "",
        f"{GRAY}windows system check  {RESET}{CYAN}{BOLD}{VERSION}{RESET}",
        f"{GRAY}{dtrunc(specs, max(10, cols - len(left) - 1))}{RESET}",
        "",
        f"{draw_bar(progress, logo_w, CYAN)}  {GRAY}첫 측정 중…{RESET}",
    ]
    # 창이 로고보다 좁거나 낮으면 로고는 빼고 글자만 띄운다
    if cols >= logo_w + 4 and rows >= len(logo) + len(body) + 2:
        block = logo + body
    else:
        block = body[1:]
    top = max(0, (rows - len(block)) // 2)
    return [""] * top + [left + line if line else "" for line in block]


def show_splash(monitor: Monitor):
    """시작 로고를 SPLASH_SECONDS 동안 띄운다. 아무 키나 누르면 바로 넘어간다.

    누른 키는 읽지 않고 남겨 둔다. 로고가 뜬 사이 q 를 눌렀으면 그대로 나가게 하려는 것.
    """
    start = time.monotonic()
    while True:
        progress = min(1.0, (time.monotonic() - start) / SPLASH_SECONDS)
        size = term_size()
        draw(render_splash(monitor, size.columns, size.lines, progress), size.columns, size.lines)
        if progress >= 1.0 or key_waiting(FRAME_SECONDS):
            return


def render_outro(grid: list, cols: int, rows: int, t: float) -> list:
    """나갈 때 연출의 한 장. grid 는 마지막 화면을 칸으로 푼 것, t 는 연출 시작 뒤 흐른 초."""
    out = [""] * rows
    mid = rows // 2
    white = (255, 255, 255)
    line_glyph = "=" if USE_ASCII else "━"

    def mix(a, b, k):
        return tuple(round(x + (y - x) * k) for x, y in zip(a, b))

    if t < OUTRO_SQUEEZE:
        # 위아래로 눌린다. 처음엔 천천히, 끝에선 확 닫힌다. 눌릴수록 글자가 하얗게 달아오른다
        s = t / OUTRO_SQUEEZE
        height = max(1, round(rows * (1 - s * s)))
        top = mid - height // 2
        glow = 0.9 * s
        for i in range(height):
            src = grid[min(rows - 1, i * rows // height)]
            out[top + i] = from_cells([
                [ch, (mix(fg or DEFAULT_FG, white, glow), bg and mix(bg, (0, 0, 0), s), bold)]
                for ch, (fg, bg, bold) in src
            ])
        return out
    t -= OUTRO_SQUEEZE
    if t < OUTRO_SHRINK:
        # 빛나는 가로줄이 가운데로 줄어든다
        s = ease_out(t / OUTRO_SHRINK)
        width = max(1, round(cols * (1 - s)))
        out[mid] = " " * ((cols - width) // 2) + rgb(mix(OUTRO_LINE, OUTRO_EMBER, s)) + line_glyph * width + RESET
        return out
    # 남은 한 점이 사그라든다
    s = min(1.0, (t - OUTRO_SHRINK) / OUTRO_FADE)
    out[mid] = " " * (cols // 2) + rgb(OUTRO_EMBER, 1 - s) + line_glyph + RESET
    return out


def play_outro(monitor: Monitor):
    """q 로 나갈 때 브라운관 TV 를 끄듯 화면을 닫는다. 아무 키나 누르면 바로 끝낸다."""
    size = term_size()
    cols, rows = size.columns, size.lines
    lines = monitor.render(cols, rows)[:rows]
    grid = [to_cells(line, cols) for line in lines]
    while len(grid) < rows:
        grid.append(to_cells("", cols))
    total = OUTRO_SQUEEZE + OUTRO_SHRINK + OUTRO_FADE
    start = time.monotonic()
    while True:
        t = time.monotonic() - start
        if t >= total:
            break
        draw(render_outro(grid, cols, rows, t), cols, rows)
        if key_waiting(FRAME_SECONDS):
            while msvcrt.kbhit():  # 누른 키는 먹어 둔다. 남기면 나간 뒤 셸에 찍힌다
                msvcrt.getwch()
            break
    draw([""] * rows, cols, rows)


def print_version() -> int:
    """--version. 터미널이면 로고와 함께, 파일·파이프면 한 줄로 찍는다 (스크립트가 읽기 쉽게)."""
    plain = f"wsc {VERSION}  {REPO_URL}"
    saved_mode = enable_vt() if sys.stdout.isatty() else None
    if saved_mode is None:
        print(plain)
        return 0
    logo, _ = logo_lines()
    print()
    for line in logo:
        print(f"  {line}")
    print(f"\n  {GRAY}windows system check  {RESET}{CYAN}{BOLD}{VERSION}{RESET}")
    print(f"  {GRAY}{REPO_URL}{RESET}\n")
    restore_console_mode(saved_mode)
    return 0


def run_interactive(monitor: Monitor, show_logo: bool = True) -> int:
    saved_mode = enable_vt()
    if saved_mode is None:
        print(
            "이 콘솔은 화면 제어 문자(ANSI)를 지원하지 않습니다. "
            "Windows 10 이상에서 Windows Terminal 로 실행하세요.",
            file=sys.stderr,
        )
        return 1

    sys.stdout.write(ALT_SCREEN_ON + CURSOR_HIDE)
    sys.stdout.flush()
    # 창 제목은 측정값으로 바꿔 쓰다가 나갈 때 원래대로 돌려놓는다
    saved_title = ctypes.create_unicode_buffer(1024)
    has_title = kernel32.GetConsoleTitleW(saved_title, len(saved_title)) > 0
    monitor.live = True
    monitor.tween.enabled = not USE_ASCII  # 옛 콘솔은 한 장 그리는 게 느려서 애니메이션이 오히려 버벅인다

    def on_break(*_):
        raise KeyboardInterrupt

    # Ctrl-Break 는 Ctrl-C 와 따로 온다. 같은 길로 빠져나가 화면을 되돌려 놓게 한다
    signal.signal(signal.SIGBREAK, on_break)

    try:
        monitor.tick()  # 차분 계산의 기준점
        if show_logo:
            # 로고를 띄운 사이 흐른 시간으로 첫 값을 낸다. 첫 화면이 '측정 중' 으로 비지 않는다
            show_splash(monitor)
            monitor.tween.items.clear()  # 로고 뒤 첫 화면에서 막대가 0 부터 차오르게
            monitor.tick()
        size = term_size()
        draw(monitor.render(size.columns, size.lines), size.columns, size.lines)
        signals = ""
        refresh_at = 0.0  # 종료시킨 직후 한 번 더 읽을 시각

        deadline = time.monotonic() + monitor.interval
        while True:
            fresh = monitor.window_signals()
            if fresh != signals:
                signals = fresh
                sys.stdout.write(fresh)
            # 키 검사를 먼저, 조건 없이 한다. 한 장 그리는 시간이 갱신 주기보다 길어지면
            # 갱신 분기에만 걸려서 키가 영영 안 읽히기 때문이다.
            # 막대가 미끄러지거나 그래프가 흐르는 등 연출 중이면 다음 장 그릴 때까지만 기다린다
            now = time.monotonic()
            remaining = max(0.0, deadline - now)
            frame = monitor.frame_wait(now)
            if frame is not None:
                remaining = min(remaining, frame)
            if refresh_at:
                remaining = min(remaining, max(0.0, refresh_at - now))
            if key_waiting(remaining):
                quit_now = False
                while msvcrt.kbhit():  # 밀린 키는 한 번에 다 처리한다
                    if not monitor.handle_key(read_key()):
                        quit_now = True
                        break
                if quit_now:
                    # 로고를 띄우는 설정이면 나갈 때도 연출로 닫는다. --no-logo 면 바로 나간다
                    if show_logo and not USE_ASCII:
                        play_outro(monitor)
                    break
                # 주기를 바꿨으면 다음 갱신 시점도 다시 잡는다
                deadline = min(deadline, time.monotonic() + monitor.interval)

            if monitor.needs_refresh:
                # 프로세스를 종료시킨 직후. 목록에서 바로 빠지게 곧 다시 읽는다. 강제 종료도
                # 프로세스가 실제로 끝나기까지 잠깐 걸려서, 바로 읽으면 아직 목록에 남아 있다
                monitor.needs_refresh = False
                refresh_at = time.monotonic() + KILL_REFRESH_DELAY
            if refresh_at and time.monotonic() >= refresh_at:
                refresh_at = 0.0
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
        sys.stdout.write((TASKBAR_CLEAR if TASKBAR else "") + CURSOR_SHOW + ALT_SCREEN_OFF)
        sys.stdout.flush()
        if has_title:
            kernel32.SetConsoleTitleW(saved_title.value)
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
        print(f"\n실패: 서버가 요청을 거절했습니다 (HTTP {exc.code}). 저장소가 비공개로 바뀌었거나 주소가 달라졌을 수 있습니다.")
        return 1
    except Exception as exc:
        print(f"\n실패: 내려받지 못했습니다 ({exc}). 인터넷 연결을 확인하세요.")
        return 1

    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        print("\n실패: 받은 파일이 손상되어 있습니다. 잠시 뒤 다시 시도하세요.")
        return 1

    found = re.search(r'^VERSION = "([^"]+)"', text, re.M)
    latest = found.group(1) if found else ""
    print(f"최신 버전  {latest or '표시 없음'}")

    with open(target, "rb") as fp:
        current = fp.read()

    # 깃이 줄 끝을 CRLF 로 바꿔 받았을 수 있다. 줄 끝만 다른 건 같은 파일로 본다
    if current.replace(b"\r\n", b"\n") == payload.replace(b"\r\n", b"\n"):
        print("\n이미 최신 버전입니다.")
        return 0
    if not latest:
        print("\n받은 파일에 버전 정보가 없어 안전을 위해 덮어쓰지 않았습니다.")
        print(f"직접 확인하세요: {REPO_URL}")
        return 1
    if parse_version(latest) < parse_version(VERSION):
        print(f"\n서버 버전이 더 낮아 덮어쓰지 않았습니다 ({latest} < {VERSION}).")
        return 1
    if check_only:
        print(f"\n새 버전 {latest} 이 나왔습니다. 설치하려면: wsc --update")
        return 0

    # 문법이 깨진 파일로 덮어쓰면 프로그램이 아예 안 열린다. 미리 검사한다
    try:
        compile(text, target, "exec")
    except SyntaxError as exc:
        print(f"\n실패: 받은 파일에 문법 오류가 있어 덮어쓰지 않았습니다 ({exc}).")
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
        print(f"\n실패: {target} 에 쓸 권한이 없습니다.")
        print("시작 메뉴에서 터미널을 '관리자 권한으로 실행'한 뒤 다시 시도하세요.")
        return 1
    except OSError as exc:
        print(f"\n실패: 파일을 바꾸지 못했습니다 ({exc}).")
        return 1

    print(f"\n{VERSION} → {latest} 갱신 완료.")
    print(f"이전 버전은 {backup} 에 백업했습니다. 문제가 없으면 지워도 됩니다.")
    return 0


def main():
    global USE_ASCII, TASKBAR

    parser = argparse.ArgumentParser(
        prog="wsc",
        description="Windows 의 CPU·메모리·네트워크 사용량과 자원을 많이 쓰는 프로세스를 터미널에 보여줍니다.",
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
        "--check-update", action="store_true", help="새 버전이 있는지 확인만 한다 (설치하지 않음)"
    )
    parser.add_argument("-v", "--version", action="store_true", help="설치된 버전 보기")
    parser.add_argument(
        "--no-check", action="store_true", help="실행할 때 새 버전 확인을 건너뛴다"
    )
    parser.add_argument("--no-logo", action="store_true", help="시작 로고와 나갈 때 연출을 건너뛴다")
    args = parser.parse_args()

    if args.version:
        if sys.stdout.isatty():
            USE_ASCII = args.ascii or (not args.unicode and wants_ascii())
        return print_version()
    if args.update or args.check_update:
        return self_update(check_only=args.check_update)

    interval = min(INTERVAL_MAX, max(INTERVAL_MIN, args.interval))
    monitor = Monitor(interval, args.sort)
    if not args.no_check:
        monitor.start_version_check()
    if sys.stdout.isatty() and sys.stdin.isatty():
        USE_ASCII = args.ascii or (not args.unicode and wants_ascii())
        TASKBAR = not os.environ.get("TERM_PROGRAM")
        return run_interactive(monitor, show_logo=not args.no_logo)
    USE_ASCII = not args.unicode  # 파일·파이프는 코드 페이지에 없는 막대 글자가 ? 로 깨진다
    return run_once(monitor)


if __name__ == "__main__":
    sys.exit(main())
