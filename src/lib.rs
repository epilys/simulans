//
// ____
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
//
// This file is part of ____.
//
// ____ is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ____ is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ____. If not, see <http://www.gnu.org/licenses/>.
//
// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

pub mod frontend;
pub mod jit;

// square:
//  sub	sp, sp, #0x10
//  str	w0, [sp, #12]
//  ldr	w8, [sp, #12]
//  ldr	w9, [sp, #12]
//  mul	w0, w8, w9
//  add	sp, sp, #0x10
//  ret
