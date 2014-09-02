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

BOOST_AUTO_TEST_SUITE(SC_test)

BOOST_AUTO_TEST_CASE(fib_simple_n2_sc){
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@i = global i32 1, align 4
@j = global i32 1, align 4

define i8* @p1(i8* %arg){
  %1 = load i32* @i, align 4
  %2 = load i32* @j, align 4
  %3 = add i32 %1, %2
  store i32 %3, i32* @i, align 4
  %4 = load i32* @i, align 4
  %5 = load i32* @j, align 4
  %6 = add i32 %4, %5
  store i32 %6, i32* @i, align 4
  ret i8* null
}

define i8* @p2(i8* %arg){
  %1 = load i32* @i, align 4
  %2 = load i32* @j, align 4
  %3 = add i32 %1, %2
  store i32 %3, i32* @j, align 4
  %4 = load i32* @i, align 4
  %5 = load i32* @j, align 4
  %6 = add i32 %4, %5
  store i32 %6, i32* @j, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p1, i8* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p2, i8* null)

  ;load i32* @i, align 4
  ;load i32* @j, align 4
  ret i32 0
}

%attr_t = type { i64, [48 x i8] }
declare i32 @pthread_create(i64*, %attr_t*, i8*(i8*)*, i8*) nounwind
declare void @__assert_fail() nounwind noreturn
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0;
  CPid P1 = P0.spawn(0);
  CPid P2 = P0.spawn(1);
  IID<CPid>
    JA(P1,2), IA(P1,4), JB(P1,6), IB(P1,8),
    ia(P2,1), ja(P2,4), ib(P2,5), jb(P2,8);
  DPORDriver_test::trace_set_spec expected =
    {{{IB,ia},{JB,ja}},                                 // 01: JIJIijij
     {{IA,ia},{ia,IB},{IB,ib},{JB,ja}},                 // 02: JIJiIjij
     {{IA,ia},{JB,ja},{ib,IB}},                         // 03: JIJijiIj
     {{IA,ia},{ja,JB},{IB,ib}},                         // 04: JIijJIij
     {{IA,ia},{ja,JB},{ib,IB},{JB,jb}},                 // 05: JIijJiIj
     {{IA,ia},{jb,JB}},                                 // 06: JIijijJI
     {{ia,IA},{JB,ja},{IB,ib}},                         // 07: JiIJIjij
     {{ia,IA},{JB,ja},{ib,IB}},                         // 08: JiIJjiIj
     {{ia,IA},{JA,ja},{ja,JB},{IB,ib}},                 // 09: JiIjJIij
     {{ia,IA},{JA,ja},{ja,JB},{IA,ib},{ib,IB},{JB,jb}}, // 10: JiIjJiIj
     {{ia,IA},{JA,ja},{IA,ib},{jb,JB}},                 // 11: JiIjijJI
     {{JA,ja},{ib,IA},{JB,jb}},                         // 12: JijiIJIj
     {{JA,ja},{ib,IA},{jb,JB}},                         // 13: JijiIjJI
     {{ja,JA},{IB,ib}},                                 // 14: ijJIJIij
     {{ja,JA},{IA,ib},{ib,IB},{JB,jb}},                 // 15: ijJIJiIj
     {{ja,JA},{IA,ib},{jb,JB}},                         // 16: ijJIijJI
     {{ja,JA},{ib,IA},{JB,jb}},                         // 17: ijJiIJIj
     {{ja,JA},{ib,IA},{JA,jb},{jb,JB}},                 // 18: ijJiIjJI
     {{jb,JA}}                                          // 19: ijijJIJI
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Intrinsic_2){
  /* Regression test: This test identifies an error where unknown
   * intrinsic functions would interfere with dryruns in
   * TSOInterpreter::run. The error would only occur when the
   * intrinsic functions reappear in the module as the module is
   * reparsed by DPORDriver. This happens every 1000 runs. The error
   * would cause crashes.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define i8* @p(i8* %arg){
  call void @llvm.dbg.declare(metadata !{i8* %arg}, metadata !0)
  store i32 1, i32* @x, align 4
  call void @llvm.dbg.declare(metadata !{i8* %arg}, metadata !0)
  store i32 2, i32* @x, align 4
  call void @llvm.dbg.declare(metadata !{i8* %arg}, metadata !0)
  store i32 3, i32* @x, align 4
  call void @llvm.dbg.declare(metadata !{i8* %arg}, metadata !0)
  ret i8* null
}

define i32 @main(){
  %T0 = alloca i64
  %T1 = alloca i64
  call i32 @pthread_create(i64* %T0, %attr_t* null, i8*(i8*)*@p, i8*null)
  call i32 @pthread_create(i64* %T1, %attr_t* null, i8*(i8*)*@p, i8*null)
  call i8* @p(i8* null)
  %T0val = load i64* %T0
  %T1val = load i64* %T1
  call i32 @pthread_join(i64 %T0val,i8** null)
  call i32 @pthread_join(i64 %T1val,i8** null)
  ret i32 0
}

%attr_t = type { i64, [48 x i8] }
declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone
declare i32 @pthread_create(i64*, %attr_t*, i8*(i8*)*, i8*) nounwind
declare i32 @pthread_join(i64,i8**) nounwind

!0 = metadata !{i32 0}
)",conf);
  DPORDriver::Result res = driver->run();
  delete driver;

  /* Number of mazurkiewicz traces: (3*3)!/(3!^3) = 1680 */
  BOOST_CHECK(res.trace_count == 1680);
}

BOOST_AUTO_TEST_CASE(Atomic_1){
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define i8* @p1(i8* %arg){
  %x = load i32* @x, align 4
  %xcmp = icmp eq i32 %x, 1
  br i1 %xcmp, label %error, label %exit
error:
  call void @__assert_fail()
  br label %exit
exit:
  ret i8* null
}

define void @__VERIFIER_atomic_updx(){
  store i32 1, i32* @x, align 4
  store i32 0, i32* @x, align 4
  ret void
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p1, i8* null)
  call void @__VERIFIER_atomic_updx()
  ret i32 0
}

%attr_t = type {i64, [48 x i8]}
declare i32 @pthread_create(i64*, %attr_t*, i8*(i8*)*, i8*) nounwind
declare void @__assert_fail()
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> ux0(P0,2), rx1(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {{{ux0,rx1}},{{rx1,ux0}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_3){
  /* Multiple different memory locations */
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4
@y = global i32 0, align 4

define i8* @p1(i8* %arg){
  load i32* @x, align 4
  load i32* @y, align 4
  ret i8* null
}

define void @__VERIFIER_atomic_updx(){
  store i32 1, i32* @x, align 4
  store i32 1, i32* @y, align 4
  ret void
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p1, i8* null)
  call void @__VERIFIER_atomic_updx()
  ret i32 0
}

%attr_t = type {i64, [48 x i8]}
declare i32 @pthread_create(i64*, %attr_t*, i8*(i8*)*, i8*) nounwind
declare void @__assert_fail()
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> uxy0(P0,2), rx1(P1,1), ry1(P1,2);
  DPORDriver_test::trace_set_spec expected =
    {{{uxy0,rx1}},{{rx1,uxy0},{uxy0,ry1}},{{ry1,uxy0}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_5){
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define void @__VERIFIER_atomic_wx(){
  store i32 2, i32* @x, align 4
  ret void
}

define i8* @p(i8* %arg){
  %foo = alloca i32, align 4
  store i32 0, i32* %foo, align 4
  call void @__VERIFIER_atomic_wx()
  load i32* @x
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p, i8* null)
  call i8* @p(i8* null)
  ret i32 0
}

%attr_t = type{i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare void @__VERIFIER_assume(i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> wx0(P0,5), rx0(P0,6),
    wx1(P1,3), rx1(P1,4);
  DPORDriver_test::trace_set_spec expected =
    {{{wx0,wx1},{rx0,wx1}},
     {{wx0,wx1},{wx1,rx0}},
     {{wx1,wx0},{rx1,wx0}},
     {{wx1,wx0},{wx0,rx1}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_6){
  /* Blocking call inside atomic function */
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define void @__VERIFIER_atomic_block(){
  call void @__VERIFIER_assume(i32 0)
  ret void
}

define void @p3(){
  store i32 1, i32* @x, align 4
  store i32 2, i32* @x, align 4
  ret void
}

define void @p2(){
  call void @p3()
  ret void
}

define i8* @p(i8* %arg){
  call void @p2()
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p, i8* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p, i8* null)
  call void @__VERIFIER_atomic_block()
  ret i32 0
}

%attr_t = type{i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare void @__VERIFIER_assume(i32)
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0); CPid P2 = P0.spawn(1);
  IID<CPid>
    wx1a(P1,3), wx1b(P1,4),
    wx2a(P2,3), wx2b(P2,4);
  DPORDriver_test::trace_set_spec expected =
    {{{wx1b,wx2a}},
     {{wx1a,wx2a},{wx2a,wx1b},{wx1b,wx2b}},
     {{wx1a,wx2a},{wx2b,wx1b}},
     {{wx2a,wx1a},{wx1b,wx2b}},
     {{wx2a,wx1a},{wx1a,wx2b},{wx2b,wx1b}},
     {{wx2b,wx1a}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_7){
  /* Blocking call inside atomic function */
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define void @__VERIFIER_atomic_block(){
  %x = load i32* @x, align 4
  call void @__VERIFIER_assume(i32 %x)
  ret void
}

define i8* @p(i8* %arg){
  store i32 1, i32* @x, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p, i8* null)
  call void @__VERIFIER_atomic_block()
  ret i32 0
}

%attr_t = type{i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare void @__VERIFIER_assume(i32)
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0); CPid P2 = P0.spawn(1);
  IID<CPid> rx0(P0,2), wx1(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {{{wx1,rx0}},{{rx0,wx1}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_8){
  /* Read depending on read depending on store, all inside atomic
   * function. */
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define void @__VERIFIER_atomic_f(){
  load i32* @x, align 4
  %p = alloca i32*, align 8
  store i32* @x, i32** %p, align 8
  %addr = load i32** %p, align 8
  load i32* %addr, align 4
  ret void
}

define i8* @p1(i8* %arg){
  store i32 1, i32* @x, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p1, i8* null)
  call void @__VERIFIER_atomic_f()
  ret i32 0
}

%attr_t = type{i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> x0(P0,2), x1(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {{{x0,x1}},{{x1,x0}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Atomic_9){
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define void @__VERIFIER_atomic_foox(){
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 1, i32* %y, align 4
  store i32 1, i32* %z, align 4
  store i32 2, i32* @x, align 4
  ret void
}

define i8* @p(i8* %arg){
  %u = alloca i32, align 4
  store i32 1, i32* %u, align 4
  call void @__VERIFIER_atomic_foox()
  store i32 1, i32* @x, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p, i8* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p, i8* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)* @p, i8* null)
  ret i32 0
}

%attr_t = type{i64,[48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  BOOST_CHECK(!res.has_errors());
  /* Number of traces:
   * 6!/((2!)^3) = 90
   *
   * 3 threads, each executing two stores to x.
   */
  BOOST_CHECK(res.trace_count == 90);
}

BOOST_AUTO_TEST_CASE(Full_conflict_1){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4

define i8* @p1(i8* %arg){
  load i32* @x, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> r1(P1,1), mc0(P0,2);
  DPORDriver_test::trace_set_spec expected =
    {{{r1,mc0}},{{mc0,r1}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_2){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  load i32* @x, align 4
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> r0(P0,2), mc1(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {{{r0,mc1}},{{mc1,r0}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_3){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> mc0(P0,2), mc1(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {{{mc0,mc1}},{{mc1,mc0}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_4){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4
@y = global i32 0, align 4

define i8* @p1(i8* %arg){
  store i32 1, i32* @x, align 4
  store i32 1, i32* @x, align 4
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  store i32 1, i32* @y, align 4
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p1wx1(P1,1), p1wx2(P1,2), p1mc(P1,3),
    p0mc(P0,2), p0wy(P0,3);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p0mc,p1wx1},{p1mc,p0wy}},
      {{p0mc,p1wx1},{p0wy,p1mc}},
      {{p1wx1,p0mc},{p0mc,p1wx2},{p1mc,p0wy}},
      {{p1wx1,p0mc},{p0mc,p1wx2},{p0wy,p1mc}},
      {{p1wx2,p0mc},{p0mc,p1mc},{p1mc,p0wy}},
      {{p1wx2,p0mc},{p0mc,p1mc},{p0wy,p1mc}},
      {{p1mc,p0mc}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_6){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4
@y = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i8* @memcpy(i8* null, i8* null, i32 0)
  store i32 1, i32* @x, align 4
  store i32 1, i32* @y, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  load i32* @x
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p1mc(P1,1), p1wx(P1,2), p0rx(P0,2);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p0rx,p1mc}},
      {{p1mc,p0rx},{p0rx,p1wx}},
      {{p1wx,p0rx}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_7){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(

@x = global i32 0, align 4
@y = global i32 0, align 4

define i8* @p1(i8* %arg){
  load i32* @x
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  store i32 1, i32* @x, align 4
  store i32 1, i32* @y, align 4
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p0mc(P0,2), p0wx(P0,3), p1rx(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p1rx,p0mc}},
      {{p0mc,p1rx},{p1rx,p0wx}},
      {{p0wx,p1rx}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_8){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@lck = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i32 @pthread_mutex_lock(i32* @lck)
  call i32 @pthread_mutex_unlock(i32* @lck)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_mutex_init(i32* @lck, i32* null) nounwind
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  call i32 @pthread_mutex_lock(i32* @lck)
  call i32 @pthread_mutex_unlock(i32* @lck)
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
declare i32 @pthread_mutex_init(i32*,i32*) nounwind
declare i32 @pthread_mutex_lock(i32*) nounwind
declare i32 @pthread_mutex_unlock(i32*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p0mc(P0,3), p0lock(P0,4), p0unlock(P0,5),
    p1lock(P1,1), p1unlock(P1,2), p1mc(P1,3);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p0unlock,p1lock}},

      {{p0mc,p1lock},{p1unlock,p0lock},{p1mc,p0lock}},
      {{p1lock,p0mc},{p0mc,p1unlock},{p1unlock,p0lock},{p1mc,p0lock}},
      {{p1unlock,p0mc},{p0mc,p1mc},{p1unlock,p0lock},{p1mc,p0lock}},

      {{p0mc,p1lock},{p1unlock,p0lock},{p0lock,p1mc},{p1mc,p0unlock}},
      {{p1lock,p0mc},{p0mc,p1unlock},{p1unlock,p0lock},{p0lock,p1mc},{p1mc,p0unlock}},
      {{p1unlock,p0mc},{p0mc,p1mc},{p1unlock,p0lock},{p0lock,p1mc},{p1mc,p0unlock}},

      {{p0mc,p1lock},{p1unlock,p0lock},{p0unlock,p1mc}},
      {{p1lock,p0mc},{p0mc,p1unlock},{p1unlock,p0lock},{p0unlock,p1mc}},
      {{p1unlock,p0mc},{p0mc,p1mc},{p1unlock,p0lock},{p0unlock,p1mc}},

      {{p1mc,p0mc},{p1unlock,p0lock}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_9){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@lck = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i8* @memcpy(i8* null, i8* null, i32 0)
  call i32 @pthread_mutex_lock(i32* @lck)
  call i32 @pthread_mutex_unlock(i32* @lck)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_mutex_init(i32* @lck, i32* null) nounwind
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i32 @pthread_mutex_lock(i32* @lck)
  call i32 @pthread_mutex_unlock(i32* @lck)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
declare i32 @pthread_mutex_init(i32*,i32*) nounwind
declare i32 @pthread_mutex_lock(i32*) nounwind
declare i32 @pthread_mutex_unlock(i32*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p0mc(P0,5), p0lock(P0,3), p0unlock(P0,4),
    p1lock(P1,2), p1unlock(P1,3), p1mc(P1,1);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p1unlock,p0lock}},

      {{p1mc,p0lock},{p0unlock,p1lock},{p0mc,p1lock}},
      {{p0lock,p1mc},{p1mc,p0unlock},{p0unlock,p1lock},{p0mc,p1lock}},
      {{p0unlock,p1mc},{p1mc,p0mc},{p0unlock,p1lock},{p0mc,p1lock}},

      {{p1mc,p0lock},{p0unlock,p1lock},{p1lock,p0mc},{p0mc,p1unlock}},
      {{p0lock,p1mc},{p1mc,p0unlock},{p0unlock,p1lock},{p1lock,p0mc},{p0mc,p1unlock}},
      {{p0unlock,p1mc},{p1mc,p0mc},{p0unlock,p1lock},{p1lock,p0mc},{p0mc,p1unlock}},

      {{p1mc,p0lock},{p0unlock,p1lock},{p1unlock,p0mc}},
      {{p0lock,p1mc},{p1mc,p0unlock},{p0unlock,p1lock},{p1unlock,p0mc}},
      {{p0unlock,p1mc},{p1mc,p0mc},{p0unlock,p1lock},{p1unlock,p0mc}},

      {{p0mc,p1mc},{p0unlock,p1lock}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Full_conflict_10){
  /* This test assumes that memcpy has full memory conflict. If that
   * is no longer the case, replace the call to memcpy with any
   * function that does have a full memory conflict.
   */
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.explore_all_traces = true;
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@lck = global i32 0, align 4

define i8* @p1(i8* %arg){
  call i32 @pthread_mutex_lock(i32* @lck)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  call i32 @pthread_mutex_unlock(i32* @lck)
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_mutex_init(i32* @lck, i32* null) nounwind
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p1, i8* null)
  call i8* @memcpy(i8* null, i8* null, i32 0)
  call i32 @pthread_mutex_lock(i32* @lck)
  call i32 @pthread_mutex_unlock(i32* @lck)
  ret i32 0
}

%attr_t = type { i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind
declare i8* @memcpy(i8*, i8*, i32) nounwind
declare i32 @pthread_mutex_init(i32*,i32*) nounwind
declare i32 @pthread_mutex_lock(i32*) nounwind
declare i32 @pthread_mutex_unlock(i32*) nounwind
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0; CPid P1 = P0.spawn(0);
  IID<CPid> p0mc(P0,3), p0lock(P0,4), p0unlock(P0,5),
    p1lock(P1,1), p1unlock(P1,3), p1mc(P1,2);
  DPORDriver_test::trace_set_spec expected =
    {
      {{p0unlock,p1lock}},

      {{p0mc,p1lock},{p1unlock,p0lock}},
      {{p1lock,p0mc},{p0mc,p1mc},{p1unlock,p0lock}},
      {{p1mc,p0mc},{p0mc,p1unlock},{p1unlock,p0lock}},
      {{p1unlock,p0mc},{p1unlock,p0lock}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Intrinsic_first){
  Configuration conf = DPORDriver_test::get_sc_conf();
  DPORDriver *driver =
    DPORDriver::parseIR(R"(
@x = global i32 0, align 4

define i8* @p0(i8* %arg){
  tail call void @llvm.dbg.value(metadata !{i8* %arg}, i64 0, metadata !1)
  store i32 1, i32* @x, align 4
  ret i8* null
}

define i32 @main(){
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p0, i8* null)
  call i32 @pthread_create(i64* null, %attr_t* null, i8*(i8*)*@p0, i8* null)
  ret i32 0
}

declare void @llvm.dbg.value(metadata, i64, metadata) #1
%attr_t = type {i64, [48 x i8]}
declare i32 @pthread_create(i64*,%attr_t*,i8*(i8*)*,i8*) nounwind

!1 = metadata !{i32 0}
)",conf);

  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0, P1 = P0.spawn(0), P2 = P0.spawn(1);
  IID<CPid> wx1(P1,1), wx2(P2,1);
  DPORDriver_test::trace_set_spec expected =
    {{{wx1,wx2}},{{wx2,wx1}}};
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(Mutex_trylock_1){
  Configuration conf = DPORDriver_test::get_sc_conf();
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
