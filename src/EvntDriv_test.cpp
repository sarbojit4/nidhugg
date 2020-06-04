/* Copyright (C) 2014-2017 Carl Leonardsson
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

#ifdef HAVE_VALGRIND_VALGRIND_H
#include <valgrind/valgrind.h>
#endif
#include "Debug.h"
#include "DPORDriver.h"
#include "DPORDriver_test.h"
#include "StrModule.h"

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(EV_test)

BOOST_AUTO_TEST_CASE(simplest_sc){
  Configuration conf = DPORDriver_test::get_sc_conf();
  std::string module = StrModule::portasm(R"(
@g = dso_local global i32 0, align 4

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @_Z7messagePv(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %4 = load i32, i32* @g, align 4
  store i32 %4, i32* %3, align 4
  %5 = load i8*, i8** %2, align 8
  ret i8* %5
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @_Z6threadPv(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  store i32 2, i32* @g, align 4
  %3 = load i8*, i8** %2, align 8
  ret i8* %3
}

; Function Attrs: noinline norecurse optnone uwtable
define dso_local i32 @main() #1 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 2, i32* %3, align 4
  %4 = bitcast i32* %3 to i8*
  %5 = call i32 @_Z14qthread_createPiPFPvS0_ES0_(i32* %1, i8* (i8*)* @_Z6threadPv, i8* %4)
  %6 = bitcast i32* %1 to i8*
  %7 = call i32 @_Z14qthread_createPiPFPvS0_ES0_(i32* %2, i8* (i8*)* @_Z6threadPv, i8* %6)
  %8 = load i32, i32* %1, align 4
  call void @_Z13qthread_starti(i32 %8)
  %9 = load i32, i32* %2, align 4
  call void @_Z13qthread_starti(i32 %9)
  %10 = load i32, i32* %1, align 4
  call void @_Z12qthread_waitiPv(i32 %10, i8* null)
  %11 = load i32, i32* %2, align 4
  call void @_Z12qthread_waitiPv(i32 %11, i8* null)
  ret i32 0
}

declare dso_local i32 @_Z14qthread_createPiPFPvS0_ES0_(i32*, i8* (i8*)*, i8*) #2

declare dso_local void @_Z13qthread_starti(i32) #2

declare dso_local void @_Z12qthread_waitiPv(i32, i8*) #2
)");

  DPORDriver *driver = DPORDriver::parseIR(module, conf);
  DPORDriver::Result res = driver->run();
  delete driver;

  conf.dpor_algorithm = Configuration::OPTIMAL;
  driver = DPORDriver::parseIR(module, conf);
  DPORDriver::Result opt_res = driver->run();
  delete driver;

  CPid P0;
  CPid P1 = P0.spawn(0);
  CPid P2 = P0.spawn(1);
  IID<CPid>
    CIW(P1,3), CIIW(P2,3);
  DPORDriver_test::trace_set_spec expected =
    {{{CIW,CIIW}},
     {{CIIW,CIW}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf,&opt_res));
}

BOOST_AUTO_TEST_SUITE_END()

#endif
