/* Copyright (C) 2014 Carl Leonardsson
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
#ifdef HAVE_BOOST_UNIT_TEST_FRAMEWORK

#include "DPORDriver.h"
#include "DPORDriver_test.h"

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(TSO_test)

BOOST_AUTO_TEST_CASE(Mutex_trylock_1){
  Configuration conf = DPORDriver_test::get_tso_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@lck = global i32 0, align 4
@x = global i32 0, align 4

define i8* @p(i8* %arg){
  %lckret = call i32 @pthread_mutex_trylock(i32* @lck)
  %lcksuc = icmp eq i32 %lckret, 0
  br i1 %lcksuc, label %CS, label %exit
CS:
  store i32 1, i32* @x, align 4
  store i32 1, i32* @x, align 4
  store i32 1, i32* @x, align 4
  store i32 1, i32* @x, align 4
  call i32 @pthread_mutex_unlock(i32* @lck)
  br label %exit
exit:
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_mutex_init(i32* @lck, i32* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p, i8* null)
  call i8* @p(i8* null)
  ret i32 0
}

%attr_t = type {i64*, [48 x i8]}
declare i32 @pthread_create(i64*, %attr_t*, i8*(i8*)*, i8*) nounwind
declare i32 @pthread_mutex_init(i32*,i32*) nounwind
declare i32 @pthread_mutex_trylock(i32*) nounwind
declare i32 @pthread_mutex_unlock(i32*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0, P1 = P0.spawn(0);
  IID<CPid> lck0(P0,4), ulck0(P0,11), lck1(P1,1), ulck1(P1,8);
  DPORDriver_test::trace_set_spec expected =
    {{{ulck0,lck1}}, // P0 entirely before P1
     {{lck0,lck1},{lck1,ulck0}}, // P0 first, P1 fails at trylock
     {{ulck1,lck0}}, // P1 entirely before P0
     {{lck1,lck0},{lck0,ulck1}} // P1 first, P0 fails at trylock
    };
  BOOST_CHECK(!res.has_errors());
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_SUITE_END()

#endif
