#!/usr/bin/env python3
"""
Virtual NES System 0.1
======================

A single-file, clean-room NES/Famicom emulator and debugger for Python 3.14.
The interface is inspired by the practical desktop layout of classic emulators:
ROM controls across the top, the game screen in the center, and live CPU/PPU
debug information on the right.

Features
--------
* Complete 256-entry Ricoh 2A03/6502 opcode map, including common unofficial
  instructions.
* NTSC Famicom timing target (60.0988 frames per second).
* Background and sprite rendering, scrolling, palettes, sprite-zero hit, DMA,
  controller ports, NMI, IRQ, and mapper IRQ support.
* Cycle-timed pulse, triangle, noise, and DMC audio with the NES nonlinear
  mixer and optional 48 kHz real-time pygame-ce output.
* iNES/NES 2.0 loading and mappers 0, 1, 2, 3, 4, 7, and 66.
* Open, reset, pause, frame-step, screenshot, scaling, and debugger controls.
* No ROMs, BIOS files, external assets, or third-party Python packages.

This is an original educational implementation, not FCEUX source code. FCEUX
has many years of hardware-accuracy work and supports far more boards, audio
edge cases, tools, and peripherals. Use ROM dumps that you are entitled to use.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import sys
import time
import tkinter as tk
from array import array
from dataclasses import dataclass
from tkinter import filedialog, messagebox, ttk
from typing import Callable, Optional


APP_TITLE = "Virtual NES System 0.1"
NTSC_FPS = 60.0988
CPU_CLOCK = 1_789_773
SCREEN_W = 256
SCREEN_H = 240

# Common NTSC 2C02 palette. Exact colors varied with display hardware.
NES_PALETTE = (
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
)


class CartridgeError(ValueError):
    """Raised when a cartridge image is malformed or unsupported."""


class Mapper:
    def __init__(self, cart: "Cartridge") -> None:
        self.cart = cart
        self.irq_pending = False

    def cpu_read(self, address: int) -> Optional[int]:
        raise NotImplementedError

    def cpu_write(self, address: int, value: int) -> bool:
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return address % len(self.cart.chr)
        return None

    def ppu_write(self, address: int, value: int) -> bool:
        if address < 0x2000 and self.cart.chr_is_ram:
            self.cart.chr[address % len(self.cart.chr)] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.cart.header_mirroring

    def clock_scanline(self) -> None:
        pass

    def reset(self) -> None:
        self.irq_pending = False


class Mapper0(Mapper):
    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None


class Mapper1(Mapper):
    """MMC1/SxROM mapper with serial bank register."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.shift = 0x10
        self.control = 0x0C
        self.chr0 = 0
        self.chr1 = 0
        self.prg_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        mode = (self.control >> 2) & 3
        bank_count = max(1, len(self.cart.prg) // 0x4000)
        if mode in (0, 1):
            bank = (self.prg_bank & 0x0E) % bank_count
            return (bank * 0x4000 + (address & 0x7FFF)) % len(self.cart.prg)
        if mode == 2:
            bank = 0 if address < 0xC000 else self.prg_bank % bank_count
        else:
            bank = self.prg_bank % bank_count if address < 0xC000 else bank_count - 1
        return (bank * 0x4000 + (address & 0x3FFF)) % len(self.cart.prg)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if value & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            return True
        complete = bool(self.shift & 1)
        self.shift = (self.shift >> 1) | ((value & 1) << 4)
        if complete:
            register = (address >> 13) & 3
            data = self.shift & 0x1F
            if register == 0:
                self.control = data
            elif register == 1:
                self.chr0 = data
            elif register == 2:
                self.chr1 = data
            else:
                self.prg_bank = data & 0x0F
            self.shift = 0x10
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if self.control & 0x10:
            bank = self.chr0 if address < 0x1000 else self.chr1
            index = bank * 0x1000 + (address & 0x0FFF)
        else:
            bank = self.chr0 & 0x1E
            index = bank * 0x1000 + address
        return index % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return ("single0", "single1", "vertical", "horizontal")[self.control & 3]


class Mapper2(Mapper):
    """UxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 0x0F
            return True
        return False


class Mapper3(Mapper):
    """CNROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper4(Mapper):
    """MMC3/MMC6-compatible banking and scanline IRQ counter."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.select = 0
        self.regs = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enabled = False

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        second_last = max(0, count - 2)
        slot = (address - 0x8000) // 0x2000
        mode = (self.select >> 6) & 1
        if slot == 0:
            bank = second_last if mode else self.regs[6]
        elif slot == 1:
            bank = self.regs[7]
        elif slot == 2:
            bank = self.regs[6] if mode else second_last
        else:
            bank = last
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
        elif region == 0xA000:
            if even and self.cart.header_mirroring != "four":
                self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        inverted = bool(self.select & 0x80)
        regions = (
            (0x0000, self.regs[0], 0x400), (0x0400, self.regs[0] + 1, 0x400),
            (0x0800, self.regs[1], 0x400), (0x0C00, self.regs[1] + 1, 0x400),
            (0x1000, self.regs[2], 0x400), (0x1400, self.regs[3], 0x400),
            (0x1800, self.regs[4], 0x400), (0x1C00, self.regs[5], 0x400),
        )
        logical = address ^ (0x1000 if inverted else 0)
        for base, bank, size in regions:
            if base <= logical < base + size:
                return (bank * 0x400 + logical - base) % len(self.cart.chr)
        return address % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_scanline(self) -> None:
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Mapper7(Mapper):
    """AxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.single = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 7
            self.single = (value >> 4) & 1
            return True
        return False

    def mirror_mode(self) -> str:
        return "single1" if self.single else "single0"


class Mapper66(Mapper):
    """GxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = (value >> 4) & 3
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


MAPPERS: dict[int, type[Mapper]] = {
    0: Mapper0,
    1: Mapper1,
    2: Mapper2,
    3: Mapper3,
    4: Mapper4,
    7: Mapper7,
    66: Mapper66,
}


class Cartridge:
    def __init__(self, image: bytes, source: str = "<memory>") -> None:
        if len(image) < 16 or image[:4] != b"NES\x1a":
            raise CartridgeError("Not a valid iNES or NES 2.0 cartridge image.")
        self.source = source
        flags6, flags7 = image[6], image[7]
        self.mapper_id = (flags6 >> 4) | (flags7 & 0xF0)
        self.nes2 = (flags7 & 0x0C) == 0x08
        if self.nes2:
            self.mapper_id |= (image[8] & 0x0F) << 8
        if flags6 & 0x08:
            self.header_mirroring = "four"
        else:
            self.header_mirroring = "vertical" if flags6 & 1 else "horizontal"
        self.battery = bool(flags6 & 2)
        offset = 16 + (512 if flags6 & 4 else 0)
        prg_banks = image[4]
        chr_banks = image[5]
        if self.nes2:
            prg_banks |= (image[9] & 0x0F) << 8
            chr_banks |= (image[9] & 0xF0) << 4
        prg_size = prg_banks * 0x4000
        chr_size = chr_banks * 0x2000
        if prg_size == 0 or offset + prg_size + chr_size > len(image):
            raise CartridgeError("The ROM is truncated or has an invalid bank count.")
        self.prg = bytes(image[offset:offset + prg_size])
        offset += prg_size
        self.chr_is_ram = chr_size == 0
        self.chr = bytearray(0x2000 if self.chr_is_ram else image[offset:offset + chr_size])
        self.prg_ram = bytearray(0x2000)
        mapper_type = MAPPERS.get(self.mapper_id)
        if mapper_type is None:
            supported = ", ".join(str(number) for number in sorted(MAPPERS))
            raise CartridgeError(
                f"Mapper {self.mapper_id} is not supported in this build. "
                f"Supported mappers: {supported}."
            )
        self.mapper = mapper_type(self)

    @classmethod
    def from_file(cls, path: str | pathlib.Path) -> "Cartridge":
        file_path = pathlib.Path(path)
        return cls(file_path.read_bytes(), str(file_path))

    def cpu_read(self, address: int) -> int:
        if 0x6000 <= address < 0x8000:
            return self.prg_ram[address & 0x1FFF]
        mapped = self.mapper.cpu_read(address)
        return self.prg[mapped] if mapped is not None else 0

    def cpu_write(self, address: int, value: int) -> None:
        if 0x6000 <= address < 0x8000:
            self.prg_ram[address & 0x1FFF] = value
        else:
            self.mapper.cpu_write(address, value)

    def ppu_read(self, address: int) -> int:
        mapped = self.mapper.ppu_read(address)
        return self.chr[mapped] if mapped is not None else 0

    def ppu_write(self, address: int, value: int) -> None:
        self.mapper.ppu_write(address, value)


LENGTH_TABLE = (
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
)


class Envelope:
    """2A03 divider/decay envelope shared by pulse and noise channels."""

    def __init__(self) -> None:
        self.loop = False
        self.constant = False
        self.period = 0
        self.start = False
        self.divider = 0
        self.decay = 0

    def write(self, value: int) -> None:
        self.loop = bool(value & 0x20)
        self.constant = bool(value & 0x10)
        self.period = value & 0x0F

    def restart(self) -> None:
        self.start = True

    def clock(self) -> None:
        if self.start:
            self.start = False
            self.decay = 15
            self.divider = self.period
        elif self.divider:
            self.divider -= 1
        else:
            self.divider = self.period
            if self.decay:
                self.decay -= 1
            elif self.loop:
                self.decay = 15

    @property
    def output(self) -> int:
        return self.period if self.constant else self.decay


class PulseChannel:
    DUTY_TABLE = (
        (0, 1, 0, 0, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 0, 0),
        (0, 1, 1, 1, 1, 0, 0, 0),
        (1, 0, 0, 1, 1, 1, 1, 1),
    )

    def __init__(self, channel: int) -> None:
        self.channel = channel
        self.enabled = False
        self.duty = 0
        self.sequence = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.envelope = Envelope()
        self.sweep_enabled = False
        self.sweep_period = 0
        self.sweep_negate = False
        self.sweep_shift = 0
        self.sweep_reload = False
        self.sweep_divider = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.duty = (value >> 6) & 3
            self.envelope.write(value)
        elif register == 1:
            self.sweep_enabled = bool(value & 0x80)
            self.sweep_period = (value >> 4) & 7
            self.sweep_negate = bool(value & 0x08)
            self.sweep_shift = value & 7
            self.sweep_reload = True
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        else:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.sequence = 0
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            self.sequence = (self.sequence + 1) & 7

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        self.sequence = (self.sequence + events) & 7
        self.timer = self.timer_period - remainder

    def target_period(self) -> int:
        change = self.timer_period >> self.sweep_shift if self.sweep_shift else 0
        if self.sweep_negate:
            return self.timer_period - change - (1 if self.channel == 1 else 0)
        return self.timer_period + change

    def sweep_muted(self) -> bool:
        return self.timer_period < 8 or self.target_period() > 0x7FF

    def clock_sweep(self) -> None:
        if (
            self.sweep_divider == 0
            and self.sweep_enabled
            and self.sweep_shift
            and not self.sweep_muted()
        ):
            self.timer_period = self.target_period() & 0x7FF
        if self.sweep_divider == 0 or self.sweep_reload:
            self.sweep_divider = self.sweep_period
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if (
            not self.enabled
            or not self.length
            or self.sweep_muted()
            or not self.DUTY_TABLE[self.duty][self.sequence]
        ):
            return 0
        return self.envelope.output


class TriangleChannel:
    SEQUENCE = tuple(range(15, -1, -1)) + tuple(range(16))

    def __init__(self) -> None:
        self.enabled = False
        self.control = False
        self.linear_reload_value = 0
        self.linear_reload = False
        self.linear_counter = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.sequence = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.control = bool(value & 0x80)
            self.linear_reload_value = value & 0x7F
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        elif register == 3:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.linear_reload = True

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
                self.sequence = (self.sequence + 1) & 31

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
            self.sequence = (self.sequence + events) & 31
        self.timer = self.timer_period - remainder

    def clock_linear(self) -> None:
        if self.linear_reload:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control:
            self.linear_reload = False

    def clock_length(self) -> None:
        if self.length and not self.control:
            self.length -= 1

    @property
    def output(self) -> int:
        # The triangle DAC holds its last level when either counter halts.
        return self.SEQUENCE[self.sequence]


class NoiseChannel:
    PERIOD_TABLE = (
        4, 8, 16, 32, 64, 96, 128, 160,
        202, 254, 380, 508, 762, 1016, 2034, 4068,
    )

    def __init__(self) -> None:
        self.enabled = False
        self.mode = False
        self.period = self.PERIOD_TABLE[0]
        self.timer = 0
        self.length = 0
        self.shift = 1
        self.envelope = Envelope()

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.envelope.write(value)
        elif register == 2:
            self.mode = bool(value & 0x80)
            self.period = self.PERIOD_TABLE[value & 0x0F]
        elif register == 3:
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)

    def advance_timer(self, ticks: int) -> None:
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)
        self.timer -= ticks

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if not self.enabled or not self.length or self.shift & 1:
            return 0
        return self.envelope.output


class DMCChannel:
    RATE_TABLE = (
        428, 380, 340, 320, 286, 254, 226, 214,
        190, 160, 142, 128, 106, 84, 72, 54,
    )

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.enabled = False
        self.irq_enabled = False
        self.loop = False
        self.irq = False
        self.period = self.RATE_TABLE[0]
        self.timer = 0
        self.output = 0
        self.sample_address = 0xC000
        self.sample_length = 1
        self.current_address = 0xC000
        self.bytes_remaining = 0
        self.sample_buffer: Optional[int] = None
        self.shift = 0
        self.bits_remaining = 8
        self.silence = True

    def write(self, address: int, value: int) -> None:
        if address == 0x4010:
            self.irq_enabled = bool(value & 0x80)
            self.loop = bool(value & 0x40)
            self.period = self.RATE_TABLE[value & 0x0F]
            if not self.irq_enabled:
                self.irq = False
        elif address == 0x4011:
            self.output = value & 0x7F
        elif address == 0x4012:
            self.sample_address = 0xC000 | (value << 6)
        elif address == 0x4013:
            self.sample_length = (value << 4) | 1

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        self.irq = False
        if not enabled:
            self.bytes_remaining = 0
        elif self.bytes_remaining == 0:
            self.restart()

    def restart(self) -> None:
        self.current_address = self.sample_address
        self.bytes_remaining = self.sample_length

    def _fill_buffer(self) -> None:
        if self.sample_buffer is not None or not self.bytes_remaining:
            return
        self.sample_buffer = self.bus.peek(self.current_address)
        if hasattr(self.bus, "cpu"):
            self.bus.cpu.stall += 4
        self.current_address = 0x8000 if self.current_address == 0xFFFF else self.current_address + 1
        self.bytes_remaining -= 1
        if self.bytes_remaining == 0:
            if self.loop:
                self.restart()
            elif self.irq_enabled:
                self.irq = True

    def clock_timer(self) -> None:
        self._fill_buffer()
        if self.timer:
            self.timer -= 1
            return
        self.timer = self.period - 1
        if not self.silence:
            if self.shift & 1:
                if self.output <= 125:
                    self.output += 2
            elif self.output >= 2:
                self.output -= 2
        self.shift >>= 1
        self.bits_remaining -= 1
        if self.bits_remaining == 0:
            self.bits_remaining = 8
            if self.sample_buffer is None:
                self.silence = True
            else:
                self.silence = False
                self.shift = self.sample_buffer
                self.sample_buffer = None
        self._fill_buffer()

    def advance_timer(self, ticks: int) -> None:
        self._fill_buffer()
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            if not self.silence:
                if self.shift & 1:
                    if self.output <= 125:
                        self.output += 2
                elif self.output >= 2:
                    self.output -= 2
            self.shift >>= 1
            self.bits_remaining -= 1
            if self.bits_remaining == 0:
                self.bits_remaining = 8
                if self.sample_buffer is None:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift = self.sample_buffer
                    self.sample_buffer = None
            self._fill_buffer()
        self.timer -= ticks
        self._fill_buffer()


class APU:
    """Cycle-timed NTSC Ricoh 2A03 APU with all five native sound channels."""

    SAMPLE_RATE = 48_000

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.pulse1 = PulseChannel(1)
        self.pulse2 = PulseChannel(2)
        self.triangle = TriangleChannel()
        self.noise = NoiseChannel()
        self.dmc = DMCChannel(bus)
        self.frame_cycle = 0
        self.cpu_cycle = 0
        self.five_step = False
        self.irq_inhibit = False
        self.frame_irq = False
        self.frame_reset_delay = 0
        self.sample_phase = 0
        self.samples = array("h")
        self.previous_mixed = 0.0
        self.high_pass = 0.0
        self.low_pass = 0.0

    @property
    def irq_pending(self) -> bool:
        return self.frame_irq or self.dmc.irq

    @property
    def irq_may_fire(self) -> bool:
        return (
            self.irq_pending
            or (not self.five_step and not self.irq_inhibit)
            or (self.dmc.enabled and self.dmc.irq_enabled)
        )

    @property
    def requires_cpu_sync(self) -> bool:
        return bool(
            self.dmc.enabled
            and (self.dmc.bytes_remaining or self.dmc.sample_buffer is not None or not self.dmc.silence)
        )

    def reset(self) -> None:
        self.__init__(self.bus)

    def write(self, address: int, value: int) -> None:
        value &= 0xFF
        if 0x4000 <= address <= 0x4003:
            self.pulse1.write(address & 3, value)
        elif 0x4004 <= address <= 0x4007:
            self.pulse2.write(address & 3, value)
        elif address in (0x4008, 0x400A, 0x400B):
            self.triangle.write(address & 3, value)
        elif address in (0x400C, 0x400E, 0x400F):
            self.noise.write(address & 3, value)
        elif 0x4010 <= address <= 0x4013:
            self.dmc.write(address, value)
        elif address == 0x4015:
            self.pulse1.enabled = bool(value & 0x01)
            self.pulse2.enabled = bool(value & 0x02)
            self.triangle.enabled = bool(value & 0x04)
            self.noise.enabled = bool(value & 0x08)
            if not self.pulse1.enabled:
                self.pulse1.length = 0
            if not self.pulse2.enabled:
                self.pulse2.length = 0
            if not self.triangle.enabled:
                self.triangle.length = 0
            if not self.noise.enabled:
                self.noise.length = 0
            self.dmc.set_enabled(bool(value & 0x10))
        elif address == 0x4017:
            self.five_step = bool(value & 0x80)
            self.irq_inhibit = bool(value & 0x40)
            if self.irq_inhibit:
                self.frame_irq = False
            # Hardware applies the new sequence after 3 or 4 CPU cycles.
            self.frame_reset_delay = 3 if self.cpu_cycle & 1 else 4

    def read_status(self) -> int:
        value = 0
        value |= int(self.pulse1.length > 0)
        value |= int(self.pulse2.length > 0) << 1
        value |= int(self.triangle.length > 0) << 2
        value |= int(self.noise.length > 0) << 3
        value |= int(self.dmc.bytes_remaining > 0) << 4
        value |= int(self.frame_irq) << 6
        value |= int(self.dmc.irq) << 7
        self.frame_irq = False
        return value

    def _quarter_frame(self) -> None:
        self.pulse1.envelope.clock()
        self.pulse2.envelope.clock()
        self.noise.envelope.clock()
        self.triangle.clock_linear()

    def _half_frame(self) -> None:
        self.pulse1.clock_length()
        self.pulse2.clock_length()
        self.triangle.clock_length()
        self.noise.clock_length()
        self.pulse1.clock_sweep()
        self.pulse2.clock_sweep()

    def _next_frame_event(self) -> int:
        events = (3729, 7457, 11186, 18641) if self.five_step else (3729, 7457, 11186, 14915)
        for event in events:
            if event > self.frame_cycle:
                return event
        return events[-1]

    def _handle_frame_event(self) -> None:
        if self.five_step:
            if self.frame_cycle in (3729, 11186):
                self._quarter_frame()
            elif self.frame_cycle in (7457, 18641):
                self._quarter_frame()
                self._half_frame()
            if self.frame_cycle >= 18641:
                self.frame_cycle = 0
        else:
            if self.frame_cycle in (3729, 11186):
                self._quarter_frame()
            elif self.frame_cycle in (7457, 14915):
                self._quarter_frame()
                self._half_frame()
            if self.frame_cycle >= 14915:
                if not self.irq_inhibit:
                    self.frame_irq = True
                self.frame_cycle = 0

    def _advance_timers(self, cpu_cycles: int) -> None:
        old_cycle = self.cpu_cycle
        self.cpu_cycle += cpu_cycles
        pulse_ticks = ((old_cycle & 1) + cpu_cycles) // 2
        if self.pulse1.enabled:
            self.pulse1.advance_timer(pulse_ticks)
        if self.pulse2.enabled:
            self.pulse2.advance_timer(pulse_ticks)
        if self.triangle.enabled:
            self.triangle.advance_timer(cpu_cycles)
        if self.noise.enabled:
            self.noise.advance_timer(cpu_cycles)
        if self.dmc.bytes_remaining or self.dmc.sample_buffer is not None or not self.dmc.silence:
            self.dmc.advance_timer(cpu_cycles)

    def _mix_sample(self) -> int:
        pulse_sum = self.pulse1.output + self.pulse2.output
        pulse = 95.88 / (8128.0 / pulse_sum + 100.0) if pulse_sum else 0.0
        tnd_input = (
            self.triangle.output / 8227.0
            + self.noise.output / 12241.0
            + self.dmc.output / 22638.0
        )
        tnd = 159.79 / (1.0 / tnd_input + 100.0) if tnd_input else 0.0
        mixed = pulse + tnd
        # A gentle DC blocker and reconstruction low-pass approximate the
        # analog output path while leaving digital channel timing untouched.
        self.high_pass = mixed - self.previous_mixed + 0.996 * self.high_pass
        self.previous_mixed = mixed
        self.low_pass += 0.35 * (self.high_pass - self.low_pass)
        return max(-32768, min(32767, int(self.low_pass * 47_000)))

    def step(self, cpu_cycles: int) -> None:
        remaining = cpu_cycles
        while remaining:
            to_sample = (CPU_CLOCK - self.sample_phase + self.SAMPLE_RATE - 1) // self.SAMPLE_RATE
            frame_target = self._next_frame_event()
            to_frame_event = frame_target - self.frame_cycle
            to_frame = min(
                to_frame_event,
                self.frame_reset_delay if self.frame_reset_delay else to_frame_event,
            )
            advance = min(remaining, to_sample, to_frame)
            self._advance_timers(advance)
            self.frame_cycle += advance
            self.sample_phase += advance * self.SAMPLE_RATE
            remaining -= advance
            reset_due = bool(self.frame_reset_delay and advance == self.frame_reset_delay)
            if self.frame_reset_delay:
                self.frame_reset_delay -= advance
            if self.frame_cycle == frame_target:
                self._handle_frame_event()
            if reset_due:
                self.frame_cycle = 0
                if self.five_step:
                    self._quarter_frame()
                    self._half_frame()
            if self.sample_phase >= CPU_CLOCK:
                self.sample_phase -= CPU_CLOCK
                self.samples.append(self._mix_sample())

    def drain_samples(self) -> bytes:
        if not self.samples:
            return b""
        samples = self.samples
        self.samples = array("h")
        if sys.byteorder != "little":
            samples.byteswap()
        return samples.tobytes()


class AudioOutput:
    """Optional pygame-ce/pygame streaming sink; the emulator stays usable silent."""

    def __init__(self) -> None:
        self.pygame = None
        self.channel = None
        self.available = False
        self.muted = False
        self.error = ""
        try:
            os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
            import pygame  # type: ignore[import-not-found]

            try:
                pygame.mixer.init(
                    frequency=APU.SAMPLE_RATE,
                    size=-16,
                    channels=1,
                    buffer=1024,
                    allowedchanges=0,
                )
            except TypeError:
                pygame.mixer.init(
                    frequency=APU.SAMPLE_RATE,
                    size=-16,
                    channels=1,
                    buffer=1024,
                )
            self.pygame = pygame
            self.channel = pygame.mixer.Channel(0)
            self.available = True
        except Exception as exc:
            self.error = str(exc)

    def submit(self, pcm: bytes) -> None:
        if not pcm or not self.available or self.muted or not self.pygame or not self.channel:
            return
        sound = self.pygame.mixer.Sound(buffer=pcm)
        if not self.channel.get_busy():
            self.channel.play(sound)
        elif self.channel.get_queue() is None:
            self.channel.queue(sound)

    def clear(self) -> None:
        if self.available and self.channel:
            self.channel.stop()

    def close(self) -> None:
        if self.pygame:
            try:
                self.pygame.mixer.quit()
            except Exception:
                pass


class PPU:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.bus: Optional[Bus] = None
        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_address = 0
        self.oam = bytearray(256)
        self.vram = bytearray(0x1000)
        self.palette = bytearray(32)
        self.address = 0
        self.temp_address = 0
        self.fine_x = 0
        self.write_latch = 0
        self.read_buffer = 0
        self.scroll_x = 0
        self.scroll_y = 0
        self.dot = 0
        self.scanline = 261
        self.odd_frame = False
        self.frame_number = 0
        self.frame_ready = False
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)
        self.bg_opaque = bytearray(SCREEN_W * SCREEN_H)

    def reset(self) -> None:
        self.ctrl = self.mask = self.status = 0
        self.address = self.temp_address = self.fine_x = self.write_latch = 0
        self.dot, self.scanline = 0, 261
        self.frame_ready = False

    def _nametable_index(self, address: int) -> int:
        raw = (address - 0x2000) & 0x0FFF
        table, offset = raw // 0x400, raw & 0x3FF
        mode = self.cart.mapper.mirror_mode()
        if mode == "vertical":
            physical = table & 1
        elif mode == "horizontal":
            physical = table >> 1
        elif mode == "single1":
            physical = 1
        elif mode == "four":
            physical = table
        else:
            physical = 0
        return physical * 0x400 + offset

    @staticmethod
    def _palette_index(address: int) -> int:
        index = address & 0x1F
        if index in (0x10, 0x14, 0x18, 0x1C):
            index -= 0x10
        return index

    def memory_read(self, address: int) -> int:
        address &= 0x3FFF
        if address < 0x2000:
            return self.cart.ppu_read(address)
        if address < 0x3F00:
            return self.vram[self._nametable_index(address)]
        return self.palette[self._palette_index(address)] & 0x3F

    def memory_write(self, address: int, value: int) -> None:
        address &= 0x3FFF
        value &= 0xFF
        if address < 0x2000:
            self.cart.ppu_write(address, value)
        elif address < 0x3F00:
            self.vram[self._nametable_index(address)] = value
        else:
            self.palette[self._palette_index(address)] = value & 0x3F

    def read_register(self, address: int) -> int:
        register = address & 7
        if register == 2:
            value = self.status
            self.status &= ~0x80
            self.write_latch = 0
            return value
        if register == 4:
            return self.oam[self.oam_address]
        if register == 7:
            value = self.memory_read(self.address)
            if self.address < 0x3F00:
                returned = self.read_buffer
                self.read_buffer = value
            else:
                returned = value
                self.read_buffer = self.memory_read(self.address - 0x1000)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF
            return returned
        return 0

    def write_register(self, address: int, value: int) -> None:
        register = address & 7
        value &= 0xFF
        if register == 0:
            old_nmi = bool(self.ctrl & 0x80)
            self.ctrl = value
            self.temp_address = (self.temp_address & 0x73FF) | ((value & 3) << 10)
            if not old_nmi and value & 0x80 and self.status & 0x80 and self.bus:
                self.bus.cpu.nmi_pending = True
        elif register == 1:
            self.mask = value
        elif register == 3:
            self.oam_address = value
        elif register == 4:
            self.oam[self.oam_address] = value
            self.oam_address = (self.oam_address + 1) & 0xFF
        elif register == 5:
            if self.write_latch == 0:
                self.scroll_x = value
                self.fine_x = value & 7
                self.temp_address = (self.temp_address & 0x7FE0) | (value >> 3)
            else:
                self.scroll_y = value
                self.temp_address = (
                    (self.temp_address & 0x0C1F)
                    | ((value & 7) << 12)
                    | ((value & 0xF8) << 2)
                )
            self.write_latch ^= 1
        elif register == 6:
            if self.write_latch == 0:
                self.temp_address = (self.temp_address & 0x00FF) | ((value & 0x3F) << 8)
            else:
                self.temp_address = (self.temp_address & 0x7F00) | value
                self.address = self.temp_address
            self.write_latch ^= 1
        elif register == 7:
            self.memory_write(self.address, value)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF

    def step(self, ppu_cycles: int) -> None:
        # Jump between PPU events rather than interpreting every single dot in
        # Python. CPU instructions still finish at their correct PPU position,
        # but this removes roughly 90,000 loop iterations from every frame.
        new_dot = self.dot + ppu_cycles
        if new_dot < 341:
            old_dot = self.dot
            self.dot = new_dot
            if self.scanline < 240 and old_dot < 260 <= new_dot and self.mask & 0x18:
                self.cart.mapper.clock_scanline()
            elif self.scanline == 241 and old_dot < 1 <= new_dot:
                self.status |= 0x80
                self.frame_number += 1
                self.frame_ready = True
                if self.ctrl & 0x80 and self.bus:
                    self.bus.cpu.nmi_pending = True
            elif self.scanline == 261 and old_dot < 1 <= new_dot:
                self.status &= ~0xE0
            return
        remaining = ppu_cycles
        while remaining:
            advance = min(remaining, 341 - self.dot)
            old_dot = self.dot
            self.dot += advance
            remaining -= advance
            if self.scanline < 240 and old_dot < 260 <= self.dot and self.mask & 0x18:
                self.cart.mapper.clock_scanline()
            if self.scanline == 241 and old_dot < 1 <= self.dot:
                self.status |= 0x80
                self.frame_number += 1
                self.frame_ready = True
                if self.ctrl & 0x80 and self.bus:
                    self.bus.cpu.nmi_pending = True
            elif self.scanline == 261 and old_dot < 1 <= self.dot:
                self.status &= ~0xE0
            if self.dot >= 341:
                self.dot -= 341
                self.scanline += 1
                if self.scanline > 261:
                    self.scanline = 0
                    self.odd_frame = not self.odd_frame

    def _color(self, palette_address: int) -> tuple[int, int, int]:
        return NES_PALETTE[self.memory_read(palette_address) & 0x3F]

    def render(self) -> bytearray:
        rgb = self.framebuffer
        opaque = self.bg_opaque
        palette_rgb = [
            NES_PALETTE[self.palette[self._palette_index(0x3F00 + index)] & 0x3F]
            for index in range(32)
        ]
        universal = palette_rgb[0]
        rgb[:] = bytes(universal) * (SCREEN_W * SCREEN_H)
        opaque[:] = b"\0" * len(opaque)
        show_bg = bool(self.mask & 0x08)
        show_sprites = bool(self.mask & 0x10)
        if show_bg:
            pattern_base = 0x1000 if self.ctrl & 0x10 else 0
            base_nt = self.ctrl & 3
            y = 0
            while y < SCREEN_H:
                world_y = (y + self.scroll_y) % 480
                nt_y, local_y = divmod(world_y, 240)
                tile_y, fine_y = divmod(local_y, 8)
                y_run = min(8 - fine_y, SCREEN_H - y)
                x = 0
                while x < SCREEN_W:
                    world_x = (x + self.scroll_x) % 512
                    nt_x, local_x = divmod(world_x, 256)
                    table = ((base_nt & 1) ^ nt_x) | ((((base_nt >> 1) & 1) ^ nt_y) << 1)
                    tile_x, fine_px = divmod(local_x, 8)
                    run = min(8 - fine_px, SCREEN_W - x)
                    nt_address = 0x2000 + table * 0x400
                    tile = self.memory_read(nt_address + tile_y * 32 + tile_x)
                    attribute = self.memory_read(
                        nt_address + 0x3C0 + (tile_y // 4) * 8 + tile_x // 4
                    )
                    shift = ((tile_y & 2) << 1) | (tile_x & 2)
                    palette_select = (attribute >> shift) & 3
                    for dy in range(y_run):
                        screen_y = y + dy
                        pattern_row = fine_y + dy
                        low = self.memory_read(pattern_base + tile * 16 + pattern_row)
                        high = self.memory_read(pattern_base + tile * 16 + pattern_row + 8)
                        row_start = screen_y * SCREEN_W
                        for dx in range(run):
                            screen_x = x + dx
                            if screen_x < 8 and not (self.mask & 0x02):
                                continue
                            bit = 7 - fine_px - dx
                            pixel = ((low >> bit) & 1) | (((high >> bit) & 1) << 1)
                            if pixel:
                                position = row_start + screen_x
                                opaque[position] = 1
                                color = palette_rgb[palette_select * 4 + pixel]
                                start = position * 3
                                rgb[start], rgb[start + 1], rgb[start + 2] = color
                    x += run
                y += y_run
        if show_sprites:
            height = 16 if self.ctrl & 0x20 else 8
            sprite_pattern = 0x1000 if self.ctrl & 0x08 else 0
            # Draw high OAM indices first so lower indices win overlaps.
            for sprite in range(63, -1, -1):
                base = sprite * 4
                top = self.oam[base] + 1
                tile = self.oam[base + 1]
                attributes = self.oam[base + 2]
                left = self.oam[base + 3]
                if top >= SCREEN_H or left >= SCREEN_W:
                    continue
                for sy in range(height):
                    y = top + sy
                    if y >= SCREEN_H:
                        continue
                    row = height - 1 - sy if attributes & 0x80 else sy
                    if height == 16:
                        bank = (tile & 1) * 0x1000
                        tile_number = (tile & 0xFE) + (row // 8)
                        tile_row = row & 7
                    else:
                        bank = sprite_pattern
                        tile_number = tile
                        tile_row = row
                    low = self.memory_read(bank + tile_number * 16 + tile_row)
                    high = self.memory_read(bank + tile_number * 16 + tile_row + 8)
                    for sx in range(8):
                        x = left + sx
                        if x >= SCREEN_W or (x < 8 and not (self.mask & 0x04)):
                            continue
                        bit = sx if attributes & 0x40 else 7 - sx
                        pixel = ((low >> bit) & 1) | (((high >> bit) & 1) << 1)
                        if not pixel:
                            continue
                        position = y * SCREEN_W + x
                        if sprite == 0 and opaque[position] and x < 255:
                            self.status |= 0x40
                        if attributes & 0x20 and opaque[position]:
                            continue
                        color = palette_rgb[0x10 + (attributes & 3) * 4 + pixel]
                        start = position * 3
                        rgb[start], rgb[start + 1], rgb[start + 2] = color
        return rgb


class Bus:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.ram = bytearray(0x800)
        self.ppu = PPU(cart)
        self.apu = APU(self)
        self.apu_pending_cycles = 0
        self.cpu = CPU(self)
        self.ppu.bus = self
        self.controller_state = [0, 0]
        self.controller_shift = [0, 0]
        self.controller_strobe = False

    def read(self, address: int) -> int:
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address < 0x4000:
            return self.ppu.read_register(address)
        if address == 0x4015:
            self.sync_apu()
            return self.apu.read_status()
        if address in (0x4016, 0x4017):
            port = address & 1
            if self.controller_strobe:
                value = self.controller_state[port] & 1
            else:
                value = self.controller_shift[port] & 1
                self.controller_shift[port] = (self.controller_shift[port] >> 1) | 0x80
            return 0x40 | value
        if address >= 0x8000 and self.cart.mapper_id == 0:
            prg = self.cart.prg
            return prg[(address - 0x8000) % len(prg)]
        if address >= 0x6000:
            return self.cart.cpu_read(address)
        return 0

    def peek(self, address: int) -> int:
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address >= 0x8000 and self.cart.mapper_id == 0:
            prg = self.cart.prg
            return prg[(address - 0x8000) % len(prg)]
        if address >= 0x6000:
            return self.cart.cpu_read(address)
        return 0

    def write(self, address: int, value: int) -> None:
        address &= 0xFFFF
        value &= 0xFF
        if address < 0x2000:
            self.ram[address & 0x7FF] = value
        elif address < 0x4000:
            self.ppu.write_register(address, value)
        elif address == 0x4014:
            page = value << 8
            for i in range(256):
                self.ppu.oam[(self.ppu.oam_address + i) & 0xFF] = self.read(page + i)
            self.cpu.stall += 513 + (self.cpu.total_cycles & 1)
        elif address == 0x4016:
            old_strobe = self.controller_strobe
            self.controller_strobe = bool(value & 1)
            if self.controller_strobe or old_strobe:
                self.controller_shift[:] = self.controller_state
        elif 0x4000 <= address <= 0x4017:
            self.sync_apu()
            self.apu.write(address, value)
        elif address >= 0x6000:
            self.cart.cpu_write(address, value)

    def tick(self, cpu_cycles: int) -> None:
        self.apu_pending_cycles += cpu_cycles
        self.ppu.step(cpu_cycles * 3)

    def sync_apu(self) -> None:
        if self.apu_pending_cycles:
            cycles = self.apu_pending_cycles
            self.apu_pending_cycles = 0
            self.apu.step(cycles)


# Status flags
C_FLAG = 0x01
Z_FLAG = 0x02
I_FLAG = 0x04
D_FLAG = 0x08
B_FLAG = 0x10
U_FLAG = 0x20
V_FLAG = 0x40
N_FLAG = 0x80


@dataclass(frozen=True, slots=True)
class Instruction:
    name: str
    mode: str
    cycles: int


# Every byte from $00 through $FF, row-major. The "KIL" entries are the
# hardware-jamming opcodes; unofficial NOPs retain their real operand lengths.
_OPCODE_ROWS = (
    "BRK IMP 7|ORA IZX 6|KIL IMP 2|SLO IZX 8|NOP ZP 3|ORA ZP 3|ASL ZP 5|SLO ZP 5|PHP IMP 3|ORA IMM 2|ASL ACC 2|ANC IMM 2|NOP ABS 4|ORA ABS 4|ASL ABS 6|SLO ABS 6",
    "BPL REL 2|ORA IZY 5|KIL IMP 2|SLO IZY 8|NOP ZPX 4|ORA ZPX 4|ASL ZPX 6|SLO ZPX 6|CLC IMP 2|ORA ABY 4|NOP IMP 2|SLO ABY 7|NOP ABX 4|ORA ABX 4|ASL ABX 7|SLO ABX 7",
    "JSR ABS 6|AND IZX 6|KIL IMP 2|RLA IZX 8|BIT ZP 3|AND ZP 3|ROL ZP 5|RLA ZP 5|PLP IMP 4|AND IMM 2|ROL ACC 2|ANC IMM 2|BIT ABS 4|AND ABS 4|ROL ABS 6|RLA ABS 6",
    "BMI REL 2|AND IZY 5|KIL IMP 2|RLA IZY 8|NOP ZPX 4|AND ZPX 4|ROL ZPX 6|RLA ZPX 6|SEC IMP 2|AND ABY 4|NOP IMP 2|RLA ABY 7|NOP ABX 4|AND ABX 4|ROL ABX 7|RLA ABX 7",
    "RTI IMP 6|EOR IZX 6|KIL IMP 2|SRE IZX 8|NOP ZP 3|EOR ZP 3|LSR ZP 5|SRE ZP 5|PHA IMP 3|EOR IMM 2|LSR ACC 2|ALR IMM 2|JMP ABS 3|EOR ABS 4|LSR ABS 6|SRE ABS 6",
    "BVC REL 2|EOR IZY 5|KIL IMP 2|SRE IZY 8|NOP ZPX 4|EOR ZPX 4|LSR ZPX 6|SRE ZPX 6|CLI IMP 2|EOR ABY 4|NOP IMP 2|SRE ABY 7|NOP ABX 4|EOR ABX 4|LSR ABX 7|SRE ABX 7",
    "RTS IMP 6|ADC IZX 6|KIL IMP 2|RRA IZX 8|NOP ZP 3|ADC ZP 3|ROR ZP 5|RRA ZP 5|PLA IMP 4|ADC IMM 2|ROR ACC 2|ARR IMM 2|JMP IND 5|ADC ABS 4|ROR ABS 6|RRA ABS 6",
    "BVS REL 2|ADC IZY 5|KIL IMP 2|RRA IZY 8|NOP ZPX 4|ADC ZPX 4|ROR ZPX 6|RRA ZPX 6|SEI IMP 2|ADC ABY 4|NOP IMP 2|RRA ABY 7|NOP ABX 4|ADC ABX 4|ROR ABX 7|RRA ABX 7",
    "NOP IMM 2|STA IZX 6|NOP IMM 2|SAX IZX 6|STY ZP 3|STA ZP 3|STX ZP 3|SAX ZP 3|DEY IMP 2|NOP IMM 2|TXA IMP 2|XAA IMM 2|STY ABS 4|STA ABS 4|STX ABS 4|SAX ABS 4",
    "BCC REL 2|STA IZY 6|KIL IMP 2|AHX IZY 6|STY ZPX 4|STA ZPX 4|STX ZPY 4|SAX ZPY 4|TYA IMP 2|STA ABY 5|TXS IMP 2|TAS ABY 5|SHY ABX 5|STA ABX 5|SHX ABY 5|AHX ABY 5",
    "LDY IMM 2|LDA IZX 6|LDX IMM 2|LAX IZX 6|LDY ZP 3|LDA ZP 3|LDX ZP 3|LAX ZP 3|TAY IMP 2|LDA IMM 2|TAX IMP 2|LAX IMM 2|LDY ABS 4|LDA ABS 4|LDX ABS 4|LAX ABS 4",
    "BCS REL 2|LDA IZY 5|KIL IMP 2|LAX IZY 5|LDY ZPX 4|LDA ZPX 4|LDX ZPY 4|LAX ZPY 4|CLV IMP 2|LDA ABY 4|TSX IMP 2|LAS ABY 4|LDY ABX 4|LDA ABX 4|LDX ABY 4|LAX ABY 4",
    "CPY IMM 2|CMP IZX 6|NOP IMM 2|DCP IZX 8|CPY ZP 3|CMP ZP 3|DEC ZP 5|DCP ZP 5|INY IMP 2|CMP IMM 2|DEX IMP 2|AXS IMM 2|CPY ABS 4|CMP ABS 4|DEC ABS 6|DCP ABS 6",
    "BNE REL 2|CMP IZY 5|KIL IMP 2|DCP IZY 8|NOP ZPX 4|CMP ZPX 4|DEC ZPX 6|DCP ZPX 6|CLD IMP 2|CMP ABY 4|NOP IMP 2|DCP ABY 7|NOP ABX 4|CMP ABX 4|DEC ABX 7|DCP ABX 7",
    "CPX IMM 2|SBC IZX 6|NOP IMM 2|ISC IZX 8|CPX ZP 3|SBC ZP 3|INC ZP 5|ISC ZP 5|INX IMP 2|SBC IMM 2|NOP IMP 2|SBC IMM 2|CPX ABS 4|SBC ABS 4|INC ABS 6|ISC ABS 6",
    "BEQ REL 2|SBC IZY 5|KIL IMP 2|ISC IZY 8|NOP ZPX 4|SBC ZPX 4|INC ZPX 6|ISC ZPX 6|SED IMP 2|SBC ABY 4|NOP IMP 2|ISC ABY 7|NOP ABX 4|SBC ABX 4|INC ABX 7|ISC ABX 7",
)


def _build_opcode_table() -> tuple[Instruction, ...]:
    entries: list[Instruction] = []
    for row in _OPCODE_ROWS:
        for item in row.split("|"):
            name, mode, cycles = item.split()
            entries.append(Instruction(name, mode, int(cycles)))
    if len(entries) != 256:
        raise RuntimeError(f"Opcode table has {len(entries)} entries, expected 256.")
    return tuple(entries)


OPCODES = _build_opcode_table()


class CPU:
    PAGE_CROSS_OPS = {
        "ORA", "AND", "EOR", "ADC", "LDA", "LDX", "LDY",
        "CMP", "SBC", "LAX", "LAS", "NOP",
    }
    # Hot official opcodes used by reset code and the inner loops of most games.
    # These bypass string dispatch and generic address decoding while retaining
    # exactly the same flags, memory accesses, and cycle counts.
    FAST_OPCODES = frozenset((
        0x09, 0x10, 0x18, 0x20, 0x29, 0x30, 0x38, 0x48, 0x49, 0x4C,
        0x50, 0x58, 0x60, 0x68, 0x69, 0x70, 0x78, 0x84, 0x85, 0x86,
        0x88, 0x8A, 0x8C, 0x8D, 0x8E, 0x90, 0x98, 0x9A, 0xA0, 0xA2,
        0xA4, 0xA5, 0xA6, 0xA8, 0xA9, 0xAA, 0xAC, 0xAD, 0xAE, 0xB0,
        0xB8, 0xBA, 0xC0, 0xC8, 0xC9, 0xCA, 0xD0, 0xD8, 0xE0, 0xE8,
        0xE9, 0xEA, 0xF0, 0xF8,
    ))

    def __init__(self, bus: Bus) -> None:
        self.bus = bus
        # Bound fast paths avoid an extra Python method layer on every memory
        # access (tens of thousands of accesses per emulated frame).
        self.read: Callable[[int], int] = bus.read
        self.write: Callable[[int, int], None] = bus.write
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.pc = 0
        self.p = I_FLAG | U_FLAG
        self.total_cycles = 0
        self.stall = 0
        self.nmi_pending = False
        self.irq_pending = False
        self.jammed = False
        self.last_pc = 0
        self.last_opcode = 0

    def reset(self) -> None:
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.p = I_FLAG | U_FLAG
        self.stall = 0
        self.nmi_pending = False
        self.irq_pending = False
        self.jammed = False
        self.pc = self.read16(0xFFFC)
        if self.pc == 0:
            self.pc = 0x8000

    def read16(self, address: int) -> int:
        return self.read(address) | (self.read((address + 1) & 0xFFFF) << 8)

    def push(self, value: int) -> None:
        self.write(0x100 | self.sp, value)
        self.sp = (self.sp - 1) & 0xFF

    def pop(self) -> int:
        self.sp = (self.sp + 1) & 0xFF
        return self.read(0x100 | self.sp)

    def set_flag(self, flag: int, condition: bool) -> None:
        if condition:
            self.p |= flag
        else:
            self.p &= ~flag

    def set_zn(self, value: int) -> int:
        value &= 0xFF
        self.set_flag(Z_FLAG, value == 0)
        self.set_flag(N_FLAG, bool(value & 0x80))
        return value

    def interrupt(self, vector: int, break_flag: bool = False) -> int:
        self.push(self.pc >> 8)
        self.push(self.pc & 0xFF)
        pushed = self.p | U_FLAG
        pushed = pushed | B_FLAG if break_flag else pushed & ~B_FLAG
        self.push(pushed)
        self.p = (self.p | I_FLAG | U_FLAG) & ~B_FLAG
        self.pc = self.read16(vector)
        return 7

    def _address(self, mode: str) -> tuple[Optional[int], bool]:
        page_crossed = False
        if mode in ("IMP", "ACC"):
            return None, False
        if mode == "IMM":
            address = self.pc
            self.pc = (self.pc + 1) & 0xFFFF
            return address, False
        if mode == "ZP":
            address = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            return address, False
        if mode in ("ZPX", "ZPY"):
            base = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            index = self.x if mode == "ZPX" else self.y
            return (base + index) & 0xFF, False
        if mode in ("ABS", "ABX", "ABY"):
            low = self.read(self.pc)
            high = self.read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            base = low | (high << 8)
            if mode == "ABS":
                return base, False
            index = self.x if mode == "ABX" else self.y
            address = (base + index) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "IND":
            pointer = self.read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
            # Original NMOS 6502 page-boundary wrap behavior.
            low = self.read(pointer)
            high = self.read((pointer & 0xFF00) | ((pointer + 1) & 0xFF))
            return low | (high << 8), False
        if mode == "IZX":
            zp = (self.read(self.pc) + self.x) & 0xFF
            self.pc = (self.pc + 1) & 0xFFFF
            return self.read(zp) | (self.read((zp + 1) & 0xFF) << 8), False
        if mode == "IZY":
            zp = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            base = self.read(zp) | (self.read((zp + 1) & 0xFF) << 8)
            address = (base + self.y) & 0xFFFF
            return address, (base & 0xFF00) != (address & 0xFF00)
        if mode == "REL":
            offset = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if offset & 0x80:
                offset -= 0x100
            return offset, False
        raise RuntimeError(f"Unknown addressing mode: {mode}")

    def _value(self, address: Optional[int]) -> int:
        if address is None:
            raise RuntimeError("Instruction requires an operand.")
        return self.read(address)

    def _compare(self, register: int, value: int) -> None:
        result = (register - value) & 0x1FF
        self.set_flag(C_FLAG, register >= value)
        self.set_zn(result)

    def _adc(self, value: int) -> None:
        carry = 1 if self.p & C_FLAG else 0
        total = self.a + value + carry
        result = total & 0xFF
        self.set_flag(C_FLAG, total > 0xFF)
        self.set_flag(V_FLAG, bool((~(self.a ^ value) & (self.a ^ result)) & 0x80))
        self.a = self.set_zn(result)

    def _sbc(self, value: int) -> None:
        self._adc(value ^ 0xFF)

    def _shift(self, name: str, address: Optional[int], accumulator: bool) -> int:
        value = self.a if accumulator else self._value(address)
        if name == "ASL":
            self.set_flag(C_FLAG, bool(value & 0x80))
            value = (value << 1) & 0xFF
        elif name == "LSR":
            self.set_flag(C_FLAG, bool(value & 1))
            value >>= 1
        elif name == "ROL":
            carry = 1 if self.p & C_FLAG else 0
            self.set_flag(C_FLAG, bool(value & 0x80))
            value = ((value << 1) | carry) & 0xFF
        else:
            carry = 0x80 if self.p & C_FLAG else 0
            self.set_flag(C_FLAG, bool(value & 1))
            value = (value >> 1) | carry
        value = self.set_zn(value)
        if accumulator:
            self.a = value
        elif address is not None:
            self.write(address, value)
        return value

    def _branch(self, condition: bool, offset: int) -> int:
        if not condition:
            return 0
        old = self.pc
        self.pc = (self.pc + offset) & 0xFFFF
        return 1 + int((old & 0xFF00) != (self.pc & 0xFF00))

    def _fast_execute(self, opcode: int) -> int:
        """Execute a high-frequency official opcode after its byte was fetched."""
        # Immediate loads.
        if opcode in (0xA0, 0xA2, 0xA9):
            value = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            value = self.set_zn(value)
            if opcode == 0xA0:
                self.y = value
            elif opcode == 0xA2:
                self.x = value
            else:
                self.a = value
            return 2
        # Zero-page loads and stores.
        if opcode in (0xA4, 0xA5, 0xA6, 0x84, 0x85, 0x86):
            address = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xA4:
                self.y = self.set_zn(self.read(address))
            elif opcode == 0xA5:
                self.a = self.set_zn(self.read(address))
            elif opcode == 0xA6:
                self.x = self.set_zn(self.read(address))
            elif opcode == 0x84:
                self.write(address, self.y)
            elif opcode == 0x85:
                self.write(address, self.a)
            else:
                self.write(address, self.x)
            return 3
        # Absolute loads and stores.
        if opcode in (0xAC, 0xAD, 0xAE, 0x8C, 0x8D, 0x8E):
            address = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            self.pc = (self.pc + 2) & 0xFFFF
            if opcode == 0xAC:
                self.y = self.set_zn(self.read(address))
            elif opcode == 0xAD:
                self.a = self.set_zn(self.read(address))
            elif opcode == 0xAE:
                self.x = self.set_zn(self.read(address))
            elif opcode == 0x8C:
                self.write(address, self.y)
            elif opcode == 0x8D:
                self.write(address, self.a)
            else:
                self.write(address, self.x)
            return 4
        # Relative branches.
        if opcode in (0x10, 0x30, 0x50, 0x70, 0x90, 0xB0, 0xD0, 0xF0):
            offset = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if offset & 0x80:
                offset -= 0x100
            condition = {
                0x10: not (self.p & N_FLAG), 0x30: bool(self.p & N_FLAG),
                0x50: not (self.p & V_FLAG), 0x70: bool(self.p & V_FLAG),
                0x90: not (self.p & C_FLAG), 0xB0: bool(self.p & C_FLAG),
                0xD0: not (self.p & Z_FLAG), 0xF0: bool(self.p & Z_FLAG),
            }[opcode]
            return 2 + self._branch(bool(condition), offset)
        # Immediate ALU and comparisons.
        if opcode in (0x09, 0x29, 0x49, 0x69, 0xC0, 0xC9, 0xE0, 0xE9):
            value = self.read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x09:
                self.a = self.set_zn(self.a | value)
            elif opcode == 0x29:
                self.a = self.set_zn(self.a & value)
            elif opcode == 0x49:
                self.a = self.set_zn(self.a ^ value)
            elif opcode == 0x69:
                self._adc(value)
            elif opcode == 0xC0:
                self._compare(self.y, value)
            elif opcode == 0xC9:
                self._compare(self.a, value)
            elif opcode == 0xE0:
                self._compare(self.x, value)
            else:
                self._sbc(value)
            return 2
        # Register transfers and increments/decrements.
        if opcode in (0x88, 0x8A, 0x98, 0x9A, 0xA8, 0xAA, 0xBA, 0xC8, 0xCA, 0xE8):
            if opcode == 0x88:
                self.y = self.set_zn(self.y - 1)
            elif opcode == 0x8A:
                self.a = self.set_zn(self.x)
            elif opcode == 0x98:
                self.a = self.set_zn(self.y)
            elif opcode == 0x9A:
                self.sp = self.x
            elif opcode == 0xA8:
                self.y = self.set_zn(self.a)
            elif opcode == 0xAA:
                self.x = self.set_zn(self.a)
            elif opcode == 0xBA:
                self.x = self.set_zn(self.sp)
            elif opcode == 0xC8:
                self.y = self.set_zn(self.y + 1)
            elif opcode == 0xCA:
                self.x = self.set_zn(self.x - 1)
            else:
                self.x = self.set_zn(self.x + 1)
            return 2
        # Flag operations and the official one-byte NOP.
        if opcode in (0x18, 0x38, 0x58, 0x78, 0xB8, 0xD8, 0xEA, 0xF8):
            if opcode == 0x18:
                self.p &= ~C_FLAG
            elif opcode == 0x38:
                self.p |= C_FLAG
            elif opcode == 0x58:
                self.p &= ~I_FLAG
            elif opcode == 0x78:
                self.p |= I_FLAG
            elif opcode == 0xB8:
                self.p &= ~V_FLAG
            elif opcode == 0xD8:
                self.p &= ~D_FLAG
            elif opcode == 0xF8:
                self.p |= D_FLAG
            return 2
        if opcode == 0x4C:  # JMP absolute
            self.pc = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            return 3
        if opcode == 0x20:  # JSR
            target = self.read(self.pc) | (self.read((self.pc + 1) & 0xFFFF) << 8)
            self.pc = (self.pc + 2) & 0xFFFF
            return_address = (self.pc - 1) & 0xFFFF
            self.push(return_address >> 8)
            self.push(return_address & 0xFF)
            self.pc = target
            return 6
        if opcode == 0x60:  # RTS
            low, high = self.pop(), self.pop()
            self.pc = ((low | (high << 8)) + 1) & 0xFFFF
            return 6
        if opcode == 0x48:
            self.push(self.a)
            return 3
        if opcode == 0x68:
            self.a = self.set_zn(self.pop())
            return 4
        raise RuntimeError(f"Invalid fast opcode ${opcode:02X}")

    def step(self) -> int:
        if self.stall:
            self.stall -= 1
            self.total_cycles += 1
            self.bus.tick(1)
            return 1
        if self.nmi_pending:
            self.nmi_pending = False
            cycles = self.interrupt(0xFFFA)
            self.total_cycles += cycles
            self.bus.tick(cycles)
            return cycles
        mapper_irq = self.bus.cart.mapper.irq_pending
        if self.bus.apu.requires_cpu_sync or (
            not (self.p & I_FLAG)
            and (self.bus.apu.irq_pending or self.bus.apu.irq_may_fire)
        ):
            self.bus.sync_apu()
        apu_irq = self.bus.apu.irq_pending
        if (self.irq_pending or mapper_irq or apu_irq) and not (self.p & I_FLAG):
            self.irq_pending = False
            self.bus.cart.mapper.irq_pending = False
            cycles = self.interrupt(0xFFFE)
            self.total_cycles += cycles
            self.bus.tick(cycles)
            return cycles
        if self.jammed:
            self.total_cycles += 1
            self.bus.tick(1)
            return 1

        self.last_pc = self.pc
        opcode = self.read(self.pc)
        self.last_opcode = opcode
        self.pc = (self.pc + 1) & 0xFFFF
        if opcode in self.FAST_OPCODES:
            cycles = self._fast_execute(opcode)
            self.p = (self.p | U_FLAG) & ~B_FLAG
            self.total_cycles += cycles
            self.bus.tick(cycles)
            return cycles
        instruction = OPCODES[opcode]
        address, crossed = self._address(instruction.mode)
        name = instruction.name
        cycles = instruction.cycles
        value = 0

        if name in self.PAGE_CROSS_OPS and crossed:
            cycles += 1

        if name == "ADC":
            self._adc(self._value(address))
        elif name == "AND":
            self.a = self.set_zn(self.a & self._value(address))
        elif name == "ASL":
            self._shift("ASL", address, instruction.mode == "ACC")
        elif name in ("BCC", "BCS", "BEQ", "BMI", "BNE", "BPL", "BVC", "BVS"):
            conditions = {
                "BCC": not (self.p & C_FLAG), "BCS": bool(self.p & C_FLAG),
                "BEQ": bool(self.p & Z_FLAG), "BMI": bool(self.p & N_FLAG),
                "BNE": not (self.p & Z_FLAG), "BPL": not (self.p & N_FLAG),
                "BVC": not (self.p & V_FLAG), "BVS": bool(self.p & V_FLAG),
            }
            cycles += self._branch(bool(conditions[name]), int(address or 0))
        elif name == "BIT":
            value = self._value(address)
            self.set_flag(Z_FLAG, (self.a & value) == 0)
            self.set_flag(V_FLAG, bool(value & 0x40))
            self.set_flag(N_FLAG, bool(value & 0x80))
        elif name == "BRK":
            self.pc = (self.pc + 1) & 0xFFFF
            self.interrupt(0xFFFE, True)
        elif name == "CLC":
            self.p &= ~C_FLAG
        elif name == "CLD":
            self.p &= ~D_FLAG
        elif name == "CLI":
            self.p &= ~I_FLAG
        elif name == "CLV":
            self.p &= ~V_FLAG
        elif name == "CMP":
            self._compare(self.a, self._value(address))
        elif name == "CPX":
            self._compare(self.x, self._value(address))
        elif name == "CPY":
            self._compare(self.y, self._value(address))
        elif name == "DEC":
            value = self.set_zn((self._value(address) - 1) & 0xFF)
            self.write(int(address), value)
        elif name == "DEX":
            self.x = self.set_zn(self.x - 1)
        elif name == "DEY":
            self.y = self.set_zn(self.y - 1)
        elif name == "EOR":
            self.a = self.set_zn(self.a ^ self._value(address))
        elif name == "INC":
            value = self.set_zn(self._value(address) + 1)
            self.write(int(address), value)
        elif name == "INX":
            self.x = self.set_zn(self.x + 1)
        elif name == "INY":
            self.y = self.set_zn(self.y + 1)
        elif name == "JMP":
            self.pc = int(address)
        elif name == "JSR":
            return_address = (self.pc - 1) & 0xFFFF
            self.push(return_address >> 8)
            self.push(return_address & 0xFF)
            self.pc = int(address)
        elif name == "LDA":
            self.a = self.set_zn(self._value(address))
        elif name == "LDX":
            self.x = self.set_zn(self._value(address))
        elif name == "LDY":
            self.y = self.set_zn(self._value(address))
        elif name == "LSR":
            self._shift("LSR", address, instruction.mode == "ACC")
        elif name == "NOP":
            pass
        elif name == "ORA":
            self.a = self.set_zn(self.a | self._value(address))
        elif name == "PHA":
            self.push(self.a)
        elif name == "PHP":
            self.push(self.p | B_FLAG | U_FLAG)
        elif name == "PLA":
            self.a = self.set_zn(self.pop())
        elif name == "PLP":
            self.p = (self.pop() | U_FLAG) & ~B_FLAG
        elif name == "ROL":
            self._shift("ROL", address, instruction.mode == "ACC")
        elif name == "ROR":
            self._shift("ROR", address, instruction.mode == "ACC")
        elif name == "RTI":
            self.p = (self.pop() | U_FLAG) & ~B_FLAG
            low, high = self.pop(), self.pop()
            self.pc = low | (high << 8)
        elif name == "RTS":
            low, high = self.pop(), self.pop()
            self.pc = ((low | (high << 8)) + 1) & 0xFFFF
        elif name == "SBC":
            self._sbc(self._value(address))
        elif name == "SEC":
            self.p |= C_FLAG
        elif name == "SED":
            self.p |= D_FLAG
        elif name == "SEI":
            self.p |= I_FLAG
        elif name == "STA":
            self.write(int(address), self.a)
        elif name == "STX":
            self.write(int(address), self.x)
        elif name == "STY":
            self.write(int(address), self.y)
        elif name == "TAX":
            self.x = self.set_zn(self.a)
        elif name == "TAY":
            self.y = self.set_zn(self.a)
        elif name == "TSX":
            self.x = self.set_zn(self.sp)
        elif name == "TXA":
            self.a = self.set_zn(self.x)
        elif name == "TXS":
            self.sp = self.x
        elif name == "TYA":
            self.a = self.set_zn(self.y)

        # Stable behavior of common unofficial NMOS 6502 opcodes.
        elif name == "LAX":
            self.a = self.x = self.set_zn(self._value(address))
        elif name == "SAX":
            self.write(int(address), self.a & self.x)
        elif name == "DCP":
            value = (self._value(address) - 1) & 0xFF
            self.write(int(address), value)
            self._compare(self.a, value)
        elif name == "ISC":
            value = (self._value(address) + 1) & 0xFF
            self.write(int(address), value)
            self._sbc(value)
        elif name == "SLO":
            value = self._shift("ASL", address, False)
            self.a = self.set_zn(self.a | value)
        elif name == "RLA":
            value = self._shift("ROL", address, False)
            self.a = self.set_zn(self.a & value)
        elif name == "SRE":
            value = self._shift("LSR", address, False)
            self.a = self.set_zn(self.a ^ value)
        elif name == "RRA":
            value = self._shift("ROR", address, False)
            self._adc(value)
        elif name == "ANC":
            self.a = self.set_zn(self.a & self._value(address))
            self.set_flag(C_FLAG, bool(self.a & 0x80))
        elif name == "ALR":
            self.a &= self._value(address)
            self.set_flag(C_FLAG, bool(self.a & 1))
            self.a = self.set_zn(self.a >> 1)
        elif name == "ARR":
            self.a &= self._value(address)
            self.a = ((self.a >> 1) | (0x80 if self.p & C_FLAG else 0)) & 0xFF
            self.set_zn(self.a)
            self.set_flag(C_FLAG, bool(self.a & 0x40))
            self.set_flag(V_FLAG, bool(((self.a >> 6) ^ (self.a >> 5)) & 1))
        elif name == "XAA":
            self.a = self.set_zn(self.x & self._value(address))
        elif name == "AXS":
            operand = self._value(address)
            result = (self.a & self.x) - operand
            self.set_flag(C_FLAG, result >= 0)
            self.x = self.set_zn(result)
        elif name == "LAS":
            value = self._value(address) & self.sp
            self.a = self.x = self.sp = self.set_zn(value)
        elif name in ("AHX", "SHX", "SHY", "TAS"):
            high_mask = ((int(address) >> 8) + 1) & 0xFF
            if name == "AHX":
                value = self.a & self.x & high_mask
            elif name == "SHX":
                value = self.x & high_mask
            elif name == "SHY":
                value = self.y & high_mask
            else:
                self.sp = self.a & self.x
                value = self.sp & high_mask
            self.write(int(address), value)
        elif name == "KIL":
            self.jammed = True
            self.pc = (self.pc - 1) & 0xFFFF
        else:
            raise RuntimeError(f"Opcode ${opcode:02X} ({name}) is not implemented.")

        self.p = (self.p | U_FLAG) & ~B_FLAG
        self.total_cycles += cycles
        self.bus.tick(cycles)
        return cycles


MODE_LENGTH = {
    "IMP": 1, "ACC": 1, "IMM": 2, "ZP": 2, "ZPX": 2, "ZPY": 2,
    "IZX": 2, "IZY": 2, "REL": 2, "ABS": 3, "ABX": 3, "ABY": 3, "IND": 3,
}


def disassemble(bus: Bus, start: int, lines: int = 12) -> list[str]:
    output: list[str] = []
    pc = start & 0xFFFF
    for _ in range(lines):
        opcode = bus.peek(pc)
        ins = OPCODES[opcode]
        length = MODE_LENGTH[ins.mode]
        operands = [bus.peek((pc + i) & 0xFFFF) for i in range(1, length)]
        raw = " ".join(f"{b:02X}" for b in [opcode, *operands]).ljust(8)
        if ins.mode == "IMM":
            operand = f"#$%02X" % operands[0]
        elif ins.mode == "ZP":
            operand = f"$%02X" % operands[0]
        elif ins.mode == "ZPX":
            operand = f"$%02X,X" % operands[0]
        elif ins.mode == "ZPY":
            operand = f"$%02X,Y" % operands[0]
        elif ins.mode == "IZX":
            operand = f"($%02X,X)" % operands[0]
        elif ins.mode == "IZY":
            operand = f"($%02X),Y" % operands[0]
        elif ins.mode in ("ABS", "ABX", "ABY", "IND"):
            target = operands[0] | (operands[1] << 8)
            suffix = {"ABS": "", "ABX": ",X", "ABY": ",Y", "IND": ")"}[ins.mode]
            operand = f"${target:04X}{suffix}" if ins.mode != "IND" else f"(${target:04X})"
        elif ins.mode == "REL":
            offset = operands[0] - 0x100 if operands[0] & 0x80 else operands[0]
            operand = f"${(pc + 2 + offset) & 0xFFFF:04X}"
        elif ins.mode == "ACC":
            operand = "A"
        else:
            operand = ""
        output.append(f"{pc:04X}  {raw} {ins.name} {operand}".rstrip())
        pc = (pc + length) & 0xFFFF
    return output


class NES:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.bus = Bus(cart)
        self.bus.cpu.reset()

    def reset(self) -> None:
        self.cart.mapper.reset()
        self.bus.ppu.reset()
        self.bus.apu_pending_cycles = 0
        self.bus.apu.reset()
        self.bus.cpu.reset()

    def run_frame(self) -> int:
        ppu = self.bus.ppu
        ppu.frame_ready = False
        instructions = 0
        while not ppu.frame_ready and instructions < 200_000:
            self.bus.cpu.step()
            instructions += 1
        if instructions >= 200_000:
            raise RuntimeError("Frame execution guard reached; the CPU may be jammed.")
        self.bus.sync_apu()
        ppu.render()
        return instructions


class EmulatorGUI:
    KEY_BITS = {
        "z": 0, "x": 1, "Shift_L": 2, "Shift_R": 2, "Return": 3,
        "Up": 4, "Down": 5, "Left": 6, "Right": 7,
    }

    def __init__(self, root: tk.Tk, initial_rom: Optional[str] = None) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        self.root.configure(bg="#17191c")
        self.root.minsize(720, 540)
        self.nes: Optional[NES] = None
        self.rom_path: Optional[pathlib.Path] = None
        self.running = False
        self.scale = tk.IntVar(value=2)
        self.show_debugger = tk.BooleanVar(value=True)
        self.muted = tk.BooleanVar(value=False)
        self.status_text = tk.StringVar(value="Ready — open an iNES ROM to begin")
        self.fps_text = tk.StringVar(value=f"NTSC {NTSC_FPS:.4f} Hz")
        self.audio = AudioOutput()
        self._photo: Optional[tk.PhotoImage] = None
        self._next_frame = time.perf_counter()
        self._fps_timer = time.perf_counter()
        self._frames_since_fps = 0
        self._build_style()
        self._build_menu()
        self._build_toolbar()
        self._build_layout()
        self._build_statusbar()
        self.root.bind_all("<KeyPress>", self._key_down)
        self.root.bind_all("<KeyRelease>", self._key_up)
        self.root.protocol("WM_DELETE_WINDOW", self._close)
        if initial_rom:
            self.load_rom(initial_rom)
        self.root.after(1, self._loop)

    def _build_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(".", background="#23262b", foreground="#e8e8e8")
        style.configure("TFrame", background="#23262b")
        style.configure("TLabel", background="#23262b", foreground="#e8e8e8")
        style.configure("TButton", background="#31353b", foreground="#f2f2f2", padding=5)
        style.configure("TNotebook", background="#23262b")
        style.configure("TNotebook.Tab", background="#31353b", foreground="#e8e8e8", padding=(9, 4))

    def _build_menu(self) -> None:
        menu = tk.Menu(self.root)
        file_menu = tk.Menu(menu, tearoff=False)
        file_menu.add_command(label="Open ROM…", accelerator="Ctrl+O", command=self.open_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Screenshot…", accelerator="F12", command=self.screenshot)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.destroy)
        menu.add_cascade(label="File", menu=file_menu)

        emulation = tk.Menu(menu, tearoff=False)
        emulation.add_command(label="Pause / Resume", accelerator="Space", command=self.toggle_pause)
        emulation.add_command(label="Reset", accelerator="Ctrl+R", command=self.reset)
        emulation.add_command(label="Step Frame", accelerator="F7", command=self.step_frame)
        menu.add_cascade(label="Emulation", menu=emulation)

        nes_menu = tk.Menu(menu, tearoff=False)
        scale_menu = tk.Menu(nes_menu, tearoff=False)
        for factor in (1, 2, 3):
            scale_menu.add_radiobutton(
                label=f"{factor}×", value=factor, variable=self.scale,
                command=self._resize_screen,
            )
        nes_menu.add_cascade(label="Video Scale", menu=scale_menu)
        nes_menu.add_checkbutton(
            label="Mute Audio", variable=self.muted, accelerator="Ctrl+M",
            command=self._toggle_mute,
        )
        nes_menu.add_separator()
        nes_menu.add_command(label="Controller Map", command=self.show_controls)
        menu.add_cascade(label="NES", menu=nes_menu)

        debug_menu = tk.Menu(menu, tearoff=False)
        debug_menu.add_checkbutton(
            label="Debugger Panel", variable=self.show_debugger,
            command=self._toggle_debugger,
        )
        debug_menu.add_command(label="Step Instruction", accelerator="F8", command=self.step_instruction)
        menu.add_cascade(label="Debug", menu=debug_menu)

        help_menu = tk.Menu(menu, tearoff=False)
        help_menu.add_command(label="About", command=self.show_about)
        menu.add_cascade(label="Help", menu=help_menu)
        self.root.config(menu=menu)
        self.root.bind("<Control-o>", lambda _event: self.open_rom())
        self.root.bind("<Control-r>", lambda _event: self.reset())
        self.root.bind("<F7>", lambda _event: self.step_frame())
        self.root.bind("<F8>", lambda _event: self.step_instruction())
        self.root.bind("<F12>", lambda _event: self.screenshot())
        self.root.bind("<space>", lambda _event: self.toggle_pause())
        self.root.bind(
            "<Control-m>",
            lambda _event: (self.muted.set(not self.muted.get()), self._toggle_mute()),
        )

    def _build_toolbar(self) -> None:
        toolbar = ttk.Frame(self.root, padding=(6, 5))
        toolbar.pack(fill=tk.X)
        ttk.Button(toolbar, text="Open ROM", command=self.open_rom).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Reset", command=self.reset).pack(side=tk.LEFT, padx=2)
        self.pause_button = ttk.Button(toolbar, text="Run", command=self.toggle_pause)
        self.pause_button.pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Frame", command=self.step_frame).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        ttk.Label(toolbar, text=APP_TITLE).pack(side=tk.LEFT)
        ttk.Label(toolbar, textvariable=self.fps_text).pack(side=tk.RIGHT)

    def _build_layout(self) -> None:
        self.panes = ttk.Panedwindow(self.root, orient=tk.HORIZONTAL)
        self.panes.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 4))
        self.video_frame = ttk.Frame(self.panes)
        self.screen_label = tk.Label(
            self.video_frame, bg="black", fg="#aaaaaa",
            text="VIRTUAL NES SYSTEM\n\nFile → Open ROM…",
            font=("TkFixedFont", 18), width=64, height=30,
        )
        self.screen_label.pack(fill=tk.BOTH, expand=True)
        self.panes.add(self.video_frame, weight=4)

        self.debug_frame = ttk.Frame(self.panes, width=270)
        self.debug_tabs = ttk.Notebook(self.debug_frame)
        self.debug_tabs.pack(fill=tk.BOTH, expand=True)
        cpu_tab = ttk.Frame(self.debug_tabs, padding=8)
        ppu_tab = ttk.Frame(self.debug_tabs, padding=8)
        apu_tab = ttk.Frame(self.debug_tabs, padding=8)
        self.debug_tabs.add(cpu_tab, text="CPU")
        self.debug_tabs.add(ppu_tab, text="PPU")
        self.debug_tabs.add(apu_tab, text="APU")
        self.register_text = tk.StringVar(value="No cartridge loaded")
        ttk.Label(
            cpu_tab, textvariable=self.register_text, justify=tk.LEFT,
            font=("TkFixedFont", 10),
        ).pack(anchor=tk.W, fill=tk.X)
        ttk.Separator(cpu_tab).pack(fill=tk.X, pady=8)
        ttk.Label(cpu_tab, text="Disassembly").pack(anchor=tk.W)
        self.disassembly = tk.Text(
            cpu_tab, width=34, height=20, bg="#111315", fg="#8fe388",
            insertbackground="white", relief=tk.FLAT, font=("TkFixedFont", 9),
            state=tk.DISABLED,
        )
        self.disassembly.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.ppu_text = tk.StringVar(value="No PPU state")
        ttk.Label(
            ppu_tab, textvariable=self.ppu_text, justify=tk.LEFT,
            font=("TkFixedFont", 10),
        ).pack(anchor=tk.W)
        self.apu_text = tk.StringVar(value="No APU state")
        ttk.Label(
            apu_tab, textvariable=self.apu_text, justify=tk.LEFT,
            font=("TkFixedFont", 10),
        ).pack(anchor=tk.W)
        self.panes.add(self.debug_frame, weight=1)

    def _build_statusbar(self) -> None:
        status = ttk.Frame(self.root, padding=(7, 3))
        status.pack(fill=tk.X)
        ttk.Label(status, textvariable=self.status_text).pack(side=tk.LEFT)
        ttk.Label(status, text="Z/X: A/B  Shift: Select  Enter: Start  Arrows: D-pad").pack(side=tk.RIGHT)

    def open_rom(self) -> None:
        path = filedialog.askopenfilename(
            parent=self.root,
            title="Open NES cartridge",
            filetypes=(("NES ROM", "*.nes"), ("All files", "*.*")),
        )
        if path:
            self.load_rom(path)

    def load_rom(self, path: str) -> None:
        try:
            cart = Cartridge.from_file(path)
            self.nes = NES(cart)
        except (OSError, CartridgeError) as exc:
            messagebox.showerror(APP_TITLE, str(exc), parent=self.root)
            return
        self.rom_path = pathlib.Path(path)
        self.running = True
        self.pause_button.configure(text="Pause")
        self.audio.clear()
        self._next_frame = time.perf_counter()
        audio_state = "48 kHz audio" if self.audio.available else "silent (install pygame-ce)"
        self.status_text.set(
            f"{self.rom_path.name}  |  Mapper {cart.mapper_id}  |  "
            f"PRG {len(cart.prg) // 1024} KiB  |  CHR {len(cart.chr) // 1024} KiB  |  "
            f"{audio_state}"
        )
        self.root.title(f"{APP_TITLE} — {self.rom_path.name}")
        self._update_debugger()

    def reset(self) -> None:
        if self.nes:
            self.nes.reset()
            self.audio.clear()
            self.running = True
            self.pause_button.configure(text="Pause")
            self.status_text.set(f"Reset — {self.rom_path.name if self.rom_path else ''}")

    def toggle_pause(self) -> None:
        if not self.nes:
            self.open_rom()
            return
        self.running = not self.running
        self.pause_button.configure(text="Pause" if self.running else "Run")
        self.status_text.set("Running" if self.running else "Paused")
        self._next_frame = time.perf_counter()

    def step_frame(self) -> None:
        if not self.nes:
            return
        self.running = False
        self.pause_button.configure(text="Run")
        try:
            self.nes.run_frame()
            self.nes.bus.apu.drain_samples()
            self._draw_frame()
            self._update_debugger()
            self.status_text.set(f"Frame {self.nes.bus.ppu.frame_number} (paused)")
        except RuntimeError as exc:
            self._runtime_error(exc)

    def step_instruction(self) -> None:
        if not self.nes:
            return
        self.running = False
        self.pause_button.configure(text="Run")
        self.nes.bus.cpu.step()
        self.nes.bus.apu.drain_samples()
        self.nes.bus.ppu.render()
        self._draw_frame()
        self._update_debugger()
        self.status_text.set("Stepped one CPU instruction")

    def _draw_frame(self) -> None:
        if not self.nes:
            return
        frame = self.nes.bus.ppu.framebuffer
        ppm = f"P6\n{SCREEN_W} {SCREEN_H}\n255\n".encode("ascii") + bytes(frame)
        base = tk.PhotoImage(data=ppm, format="PPM")
        factor = self.scale.get()
        self._photo = base.zoom(factor, factor) if factor > 1 else base
        self.screen_label.configure(image=self._photo, text="", width=SCREEN_W * factor, height=SCREEN_H * factor)

    def _resize_screen(self) -> None:
        if self.nes:
            self._draw_frame()

    def _toggle_debugger(self) -> None:
        if self.show_debugger.get():
            try:
                self.panes.add(self.debug_frame, weight=1)
            except tk.TclError:
                pass
        else:
            self.panes.forget(self.debug_frame)

    def _toggle_mute(self) -> None:
        self.audio.muted = self.muted.get()
        if self.audio.muted:
            self.audio.clear()
        self.status_text.set("Audio muted" if self.audio.muted else "Audio enabled")

    def _update_debugger(self) -> None:
        if not self.nes or not self.show_debugger.get():
            return
        cpu = self.nes.bus.cpu
        flags = "".join(
            letter if cpu.p & flag else "."
            for letter, flag in zip("NVUBDIZC", (N_FLAG, V_FLAG, U_FLAG, B_FLAG, D_FLAG, I_FLAG, Z_FLAG, C_FLAG))
        )
        self.register_text.set(
            f"PC  ${cpu.pc:04X}    A   ${cpu.a:02X}\n"
            f"X   ${cpu.x:02X}      Y   ${cpu.y:02X}\n"
            f"SP  ${cpu.sp:02X}      P   ${cpu.p:02X}\n"
            f"FLAGS {flags}\n"
            f"CYC {cpu.total_cycles:,}\n"
            f"OPCODES {len(OPCODES)}/256"
        )
        lines = disassemble(self.nes.bus, cpu.pc)
        self.disassembly.configure(state=tk.NORMAL)
        self.disassembly.delete("1.0", tk.END)
        self.disassembly.insert("1.0", "\n".join(("> " if i == 0 else "  ") + line for i, line in enumerate(lines)))
        self.disassembly.configure(state=tk.DISABLED)
        ppu = self.nes.bus.ppu
        self.ppu_text.set(
            f"SCANLINE {ppu.scanline:3d}\n"
            f"DOT      {ppu.dot:3d}\n"
            f"FRAME    {ppu.frame_number}\n"
            f"PPUCTRL  ${ppu.ctrl:02X}\n"
            f"PPUMASK  ${ppu.mask:02X}\n"
            f"STATUS   ${ppu.status:02X}\n"
            f"VRAM     ${ppu.address:04X}\n"
            f"SCROLL   {ppu.scroll_x:3d}, {ppu.scroll_y:3d}\n"
            f"MIRROR   {self.nes.cart.mapper.mirror_mode()}\n"
            f"MAPPER   {self.nes.cart.mapper_id}"
        )
        apu = self.nes.bus.apu
        self.apu_text.set(
            f"SAMPLE   {apu.SAMPLE_RATE:,} Hz\n"
            f"CYCLE    {apu.cpu_cycle:,}\n"
            f"SEQUENCER {'5-step' if apu.five_step else '4-step'}\n"
            f"FRAME IRQ {int(apu.frame_irq)}\n"
            f"DMC IRQ   {int(apu.dmc.irq)}\n\n"
            f"PULSE 1  {apu.pulse1.output:2d}  L={apu.pulse1.length:3d}  T={apu.pulse1.timer_period:4d}\n"
            f"PULSE 2  {apu.pulse2.output:2d}  L={apu.pulse2.length:3d}  T={apu.pulse2.timer_period:4d}\n"
            f"TRIANGLE {apu.triangle.output:2d}  L={apu.triangle.length:3d}  T={apu.triangle.timer_period:4d}\n"
            f"NOISE    {apu.noise.output:2d}  L={apu.noise.length:3d}  P={apu.noise.period:4d}\n"
            f"DMC      {apu.dmc.output:3d}  BYTES={apu.dmc.bytes_remaining:4d}\n\n"
            f"OUTPUT   {'muted' if self.audio.muted else ('active' if self.audio.available else 'unavailable')}"
        )

    def _key_down(self, event: tk.Event) -> None:
        if not self.nes:
            return
        key = event.keysym if event.keysym in self.KEY_BITS else event.char.lower()
        bit = self.KEY_BITS.get(key)
        if bit is not None:
            self.nes.bus.controller_state[0] |= 1 << bit

    def _key_up(self, event: tk.Event) -> None:
        if not self.nes:
            return
        key = event.keysym if event.keysym in self.KEY_BITS else event.char.lower()
        bit = self.KEY_BITS.get(key)
        if bit is not None:
            self.nes.bus.controller_state[0] &= ~(1 << bit)

    def screenshot(self) -> None:
        if not self.nes:
            return
        suggested = (self.rom_path.stem if self.rom_path else "virtual-nes") + ".ppm"
        path = filedialog.asksaveasfilename(
            parent=self.root, defaultextension=".ppm", initialfile=suggested,
            filetypes=(("Portable Pixmap", "*.ppm"),),
        )
        if not path:
            return
        try:
            header = f"P6\n{SCREEN_W} {SCREEN_H}\n255\n".encode("ascii")
            pathlib.Path(path).write_bytes(header + bytes(self.nes.bus.ppu.framebuffer))
            self.status_text.set(f"Screenshot saved: {pathlib.Path(path).name}")
        except OSError as exc:
            messagebox.showerror(APP_TITLE, str(exc), parent=self.root)

    def show_controls(self) -> None:
        messagebox.showinfo(
            "Controller Map",
            "Player 1\n\n"
            "D-pad: Arrow keys\n"
            "A: Z\n"
            "B: X\n"
            "Select: Shift\n"
            "Start: Enter\n\n"
            "Space pauses or resumes emulation.",
            parent=self.root,
        )

    def show_about(self) -> None:
        messagebox.showinfo(
            APP_TITLE,
            f"{APP_TITLE}\n\n"
            "Single-file Python 3.14 NES/Famicom emulator\n"
            f"Timing target: {NTSC_FPS:.4f} FPS\n"
            f"CPU opcode table: {len(OPCODES)}/256\n"
            "Audio: cycle-timed 2A03, 48 kHz nonlinear mix\n"
            "Mappers: 0, 1, 2, 3, 4, 7, 66\n\n"
            "Original clean-room educational code. No ROMs or BIOS included.",
            parent=self.root,
        )

    def _runtime_error(self, exc: Exception) -> None:
        self.running = False
        self.pause_button.configure(text="Run")
        self.status_text.set(f"Paused: {exc}")
        messagebox.showerror(APP_TITLE, str(exc), parent=self.root)

    def _close(self) -> None:
        self.audio.close()
        self.root.destroy()

    def _loop(self) -> None:
        now = time.perf_counter()
        if self.running and self.nes and now >= self._next_frame:
            try:
                self.nes.run_frame()
                self.audio.submit(self.nes.bus.apu.drain_samples())
                self._draw_frame()
                self._frames_since_fps += 1
                if self._frames_since_fps % 4 == 0:
                    self._update_debugger()
                frame_time = 1.0 / NTSC_FPS
                self._next_frame += frame_time
                if now - self._next_frame > frame_time * 3:
                    self._next_frame = now + frame_time
                elapsed = now - self._fps_timer
                if elapsed >= 1.0:
                    measured = self._frames_since_fps / elapsed
                    self.fps_text.set(f"{measured:5.1f} FPS  |  NTSC {NTSC_FPS:.4f} Hz")
                    self._fps_timer = now
                    self._frames_since_fps = 0
            except Exception as exc:  # Keep Tk alive and expose core failures.
                self._runtime_error(exc)
        delay = max(1, int((self._next_frame - time.perf_counter()) * 1000)) if self.running else 8
        self.root.after(min(delay, 16), self._loop)


def _make_test_rom() -> bytes:
    header = bytearray(b"NES\x1a" + bytes((1, 1, 0, 0)) + bytes(8))
    prg = bytearray([0xEA] * 0x4000)
    # LDX #$01; INX; STX $00; JMP $8002
    prg[:8] = bytes((0xA2, 0x01, 0xE8, 0x86, 0x00, 0x4C, 0x02, 0x80))
    prg[0x3FFA:0x4000] = bytes((0x00, 0x80, 0x00, 0x80, 0x00, 0x80))
    return bytes(header + prg + bytearray(0x2000))


def self_test() -> int:
    assert len(OPCODES) == 256
    assert all(ins.mode in MODE_LENGTH for ins in OPCODES)
    cart = Cartridge(_make_test_rom(), "<self-test>")
    nes = NES(cart)
    for _ in range(20):
        nes.bus.cpu.step()
    assert nes.bus.ram[0] > 1
    assert nes.bus.cpu.pc in range(0x8002, 0x8008)
    # Verify mapper zero mirrors a 16 KiB PRG into both CPU banks.
    assert cart.cpu_read(0x8000) == cart.cpu_read(0xC000)
    # Exercise a full PPU frame and raster output without opening a window.
    nes.run_frame()
    assert len(nes.bus.ppu.render()) == SCREEN_W * SCREEN_H * 3
    # Exercise a constant-volume pulse waveform and the 48 kHz sample clock.
    audio_nes = NES(Cartridge(_make_test_rom(), "<audio-self-test>"))
    apu = audio_nes.bus.apu
    apu.write(0x4017, 0x40)
    apu.write(0x4015, 0x01)
    apu.write(0x4000, 0xBF)  # 50% duty, loop, constant volume 15
    apu.write(0x4002, 0xFD)
    apu.write(0x4003, 0x08)
    apu.step(29_782)
    pcm = apu.drain_samples()
    assert 1_580 <= len(pcm) <= 1_610
    assert len(set(pcm)) > 8
    # Verify DMC DMA, sample exhaustion IRQ, and IRQ acknowledge behavior.
    dmc_nes = NES(Cartridge(_make_test_rom(), "<dmc-self-test>"))
    dmc = dmc_nes.bus.apu
    dmc.write(0x4010, 0x8F)
    dmc.write(0x4012, 0x00)
    dmc.write(0x4013, 0x00)
    dmc.write(0x4015, 0x10)
    dmc.step(2)
    assert dmc.dmc.irq and dmc_nes.bus.cpu.stall >= 4
    assert dmc.read_status() & 0x80
    dmc.write(0x4015, 0x00)
    assert not dmc.dmc.irq
    print(
        f"{APP_TITLE}: self-test passed "
        f"({len(OPCODES)} opcodes, mapper {cart.mapper_id}, "
        f"frame {nes.bus.ppu.frame_number}, 2A03 audio)"
    )
    return 0


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    parser.add_argument("rom", nargs="?", help="optional .nes ROM to open")
    parser.add_argument("--self-test", action="store_true", help="test the core without opening the GUI")
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        return self_test()
    root = tk.Tk()
    EmulatorGUI(root, args.rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
