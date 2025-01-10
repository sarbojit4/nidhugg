/* Copyright (C) 2021 Magnus Lång
 *
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <config.h>

#ifndef __RMW_ACTION_H__
#define __RMW_ACTION_H__

#include "SymAddr.h"

#include <utility>
#include <vector>

struct RmwAction {
  SymData::block_type operand;
  SymData::block_type oldvalue;
  enum Kind : uint8_t {
    XCHG = 1,
    ADD,
    SUB,
    AND,
    NAND,
    OR,
    XOR,
    MAX,
    MIN,
    UMAX,
    UMIN,
  } kind;
  bool result_used;
  /* True if the result is used only in the next compare instruction
   * e.g. ++x == 2 */
  bool used_only_by_cmp;
  /* Information to recompute the result of the only comparison afterwards */
  typedef std::vector<std::pair<uint_fast8_t, unsigned>> Binops;
  Binops binops;
  uint_fast8_t cmp_op;
  std::shared_ptr<uint8_t> cmp_rhs;

  RmwAction(Kind kind, SymData::block_type operand, bool result_used,
	    SymData::block_type oldvalue, bool used_only_by_cmp, Binops binops,
	    uint_fast8_t cmp_op, std::shared_ptr<uint8_t> cmp_rhs)
    : operand(std::move(operand)), oldvalue(std::move(oldvalue)), kind(kind),
    result_used(result_used), used_only_by_cmp(used_only_by_cmp),
    binops(std::move(binops)), cmp_op(cmp_op), cmp_rhs(cmp_rhs) {}

  static const char *name(Kind op);

  /* Computes the result of this rmw action when given data as input */
  void apply_to(SymData &dst, const SymData &data);
  void apply_to(void *dst, std::size_t size, void *data);
};

#endif
