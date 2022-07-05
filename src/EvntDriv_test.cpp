/* Copyright (C) 2019-2020 Sarbojit Das
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

BOOST_AUTO_TEST_CASE(nW){
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.dpor_algorithm = Configuration::EVENT_DRIVEN;
  std::string module = StrModule::portasm(R"(
@x = common dso_local global i32 0, align 4
@handler = common dso_local global i64 0, align 8

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @mes(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  store i32 2, i32* %3, align 4
  %4 = load i32, i32* %3, align 4
  store atomic i32 %4, i32* @x seq_cst, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @th_post(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i64, i64* @handler, align 8
  %4 = load i8*, i8** %2, align 8
  call void @qthread_post_event(i64 %3, void (i8*)* @mes, i8* %4)
  ret i8* null
}

declare dso_local void @qthread_post_event(i64, void (i8*)*, i8*) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @handler_func(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = call i32 (...) @qthread_exec()
  ret i8* null
}

declare dso_local i32 @qthread_exec(...) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca [3 x i64], align 16
  %3 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %4 = call i32 @qthread_create(i64* @handler, i8* (i8*)* @handler_func, i8* null)
  %5 = load i64, i64* @handler, align 8
  call void @qthread_start(i64 %5)
  store i32 0, i32* %3, align 4
  br label %6

; <label>:6:                                      ; preds = %11, %0
  %7 = load i32, i32* %3, align 4
  %8 = icmp slt i32 %7, 3
  br i1 %8, label %9, label %14

; <label>:9:                                      ; preds = %6
  %10 = load i64, i64* @handler, align 8
  call void @qthread_post_event(i64 %10, void (i8*)* @mes, i8* null)
  br label %11

; <label>:11:                                     ; preds = %9
  %12 = load i32, i32* %3, align 4
  %13 = add nsw i32 %12, 1
  store i32 %13, i32* %3, align 4
  br label %6

; <label>:14:                                     ; preds = %6
  %15 = load i32, i32* %1, align 4
  ret i32 %15
}

declare dso_local i32 @qthread_create(i64*, i8* (i8*)*, i8*) #1

declare dso_local void @qthread_start(i64) #1
)");

  DPORDriver *driver = DPORDriver::parseIR(module, conf);
  DPORDriver::Result res = driver->run();
  delete driver;

  CPid P0;
  CPid H = P0.spawn(0);
  CPid P1 = P0.spawn(1);
  CPid P2 = P0.spawn(2);
  CPid P3 = P0.spawn(3);
  IID<CPid>
    C1W(P1,6), C2W(P2,6), C3W(P3,6);
  DPORDriver_test::trace_set_spec expected =
    {{{C1W,C2W},{C2W,C3W}},
     {{C1W,C3W},{C3W,C2W}},
     {{C2W,C1W},{C1W,C3W}},
     {{C2W,C3W},{C3W,C1W}},
     {{C3W,C1W},{C1W,C2W}},
     {{C3W,C2W},{C2W,C1W}}
    };
  BOOST_CHECK(DPORDriver_test::check_all_traces(res,expected,conf));
}

BOOST_AUTO_TEST_CASE(nW_nR){
  Configuration conf = DPORDriver_test::get_sc_conf();
  conf.dpor_algorithm = Configuration::EVENT_DRIVEN;
  std::string module = StrModule::portasm(R"(
%union.pthread_attr_t = type { i64, [48 x i8] }
@g = common dso_local global i32 0, align 4
@handler = common dso_local global i64 0, align 8

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @mes1(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  store i32 1, i32* %3, align 4
  %4 = load i32, i32* %3, align 4
  store atomic i32 %4, i32* @g seq_cst, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @mes2(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %5 = load atomic i32, i32* @g seq_cst, align 4
  store i32 %5, i32* %4, align 4
  %6 = load i32, i32* %4, align 4
  store i32 %6, i32* %3, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @th_post1(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i64, i64* @handler, align 8
  %4 = load i8*, i8** %2, align 8
  call void @qthread_post_event(i64 %3, void (i8*)* @mes1, i8* %4)
  ret i8* null
}

declare dso_local void @qthread_post_event(i64, void (i8*)*, i8*) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @th_post2(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i64, i64* @handler, align 8
  %4 = load i8*, i8** %2, align 8
  call void @qthread_post_event(i64 %3, void (i8*)* @mes2, i8* %4)
  ret i8* null
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @handler_func(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = call i32 (...) @qthread_exec()
  ret i8* null
}

declare dso_local i32 @qthread_exec(...) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca [6 x i64], align 16
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %5 = call i32 @qthread_create(i64* @handler, i8* (i8*)* @handler_func, i8* null)
  %6 = load i64, i64* @handler, align 8
  call void @qthread_start(i64 %6)
  store i32 0, i32* %3, align 4
  br label %7

; <label>:7:                                      ; preds = %20, %0
  %8 = load i32, i32* %3, align 4
  %9 = icmp slt i32 %8, 6
  br i1 %9, label %10, label %23

; <label>:10:                                     ; preds = %7
  %11 = load i32, i32* %3, align 4
  %12 = add nsw i32 %11, 1
  store i32 %12, i32* %3, align 4
  %13 = sext i32 %11 to i64
  %14 = getelementptr inbounds [6 x i64], [6 x i64]* %2, i64 0, i64 %13
  %15 = call i32 @pthread_create(i64* %14, %union.pthread_attr_t* null, i8* (i8*)* @th_post1, i8* null) #3
  %16 = load i32, i32* %3, align 4
  %17 = sext i32 %16 to i64
  %18 = getelementptr inbounds [6 x i64], [6 x i64]* %2, i64 0, i64 %17
  %19 = call i32 @pthread_create(i64* %18, %union.pthread_attr_t* null, i8* (i8*)* @th_post2, i8* null) #3
  br label %20

; <label>:20:                                     ; preds = %10
  %21 = load i32, i32* %3, align 4
  %22 = add nsw i32 %21, 1
  store i32 %22, i32* %3, align 4
  br label %7

; <label>:23:                                     ; preds = %7
  store i32 0, i32* %4, align 4
  br label %24

; <label>:24:                                     ; preds = %33, %23
  %25 = load i32, i32* %4, align 4
  %26 = icmp slt i32 %25, 6
  br i1 %26, label %27, label %36

; <label>:27:                                     ; preds = %24
  %28 = load i32, i32* %4, align 4
  %29 = sext i32 %28 to i64
  %30 = getelementptr inbounds [6 x i64], [6 x i64]* %2, i64 0, i64 %29
  %31 = load i64, i64* %30, align 8
  %32 = call i32 @pthread_join(i64 %31, i8** null)
  br label %33

; <label>:33:                                     ; preds = %27
  %34 = load i32, i32* %4, align 4
  %35 = add nsw i32 %34, 1
  store i32 %35, i32* %4, align 4
  br label %24

; <label>:36:                                     ; preds = %24
  ret i32 0
}

declare dso_local i32 @qthread_create(i64*, i8* (i8*)*, i8*) #1

declare dso_local void @qthread_start(i64) #1

; Function Attrs: nounwind
declare dso_local i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #2

declare dso_local i32 @pthread_join(i64, i8**) #1
)");

  DPORDriver *driver = DPORDriver::parseIR(module, conf);
  DPORDriver::Result res = driver->run();
  BOOST_CHECK(res.trace_count == 384);
  BOOST_CHECK(!res.has_errors());
  delete driver;

}

BOOST_AUTO_TEST_SUITE_END()

#endif
