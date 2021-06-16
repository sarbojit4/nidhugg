; ModuleID = 'nR+nW.c'
source_filename = "nR+nW.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%union.pthread_attr_t = type { i64, [48 x i8] }

@x = common dso_local global i32 0, align 4
@handler1 = common dso_local global i64 0, align 8
@handler2 = common dso_local global i64 0, align 8

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @qthread_wait(i64, i8*) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i8*, align 8
  store i64 %0, i64* %3, align 8
  store i8* %1, i8** %4, align 8
  %5 = load i64, i64* %3, align 8
  %6 = load i8*, i8** %4, align 8
  %7 = bitcast i8* %6 to i8**
  %8 = call i32 @pthread_join(i64 %5, i8** %7)
  ret void
}

declare dso_local i32 @pthread_join(i64, i8**) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @mes1(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  store i32 2, i32* %3, align 4
  %4 = load i32, i32* %3, align 4
  store atomic i32 %4, i32* @x seq_cst, align 4
  ret i8* null
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @mes2(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %5 = load atomic i32, i32* @x seq_cst, align 4
  store i32 %5, i32* %4, align 4
  %6 = load i32, i32* %4, align 4
  store i32 %6, i32* %3, align 4
  ret i8* null
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @th_post1(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i64, i64* @handler1, align 8
  %4 = load i8*, i8** %2, align 8
  call void @qthread_post_event(i64 %3, i8* (i8*)* @mes1, i8* %4)
  ret i8* null
}

declare dso_local void @qthread_post_event(i64, i8* (i8*)*, i8*) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @th_post2(i8*) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i64, i64* @handler2, align 8
  %4 = load i8*, i8** %2, align 8
  call void @qthread_post_event(i64 %3, i8* (i8*)* @mes2, i8* %4)
  ret i8* null
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @handler_func(i8*) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %4 = call i32 (...) @qthread_exec()
  store i32 %4, i32* %3, align 4
  ret i8* null
}

declare dso_local i32 @qthread_exec(...) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca [2 x i64], align 16
  %3 = alloca [2 x i64], align 16
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %7 = call i32 @qthread_create(i64* @handler1, i8* (i8*)* @handler_func, i8* null)
  %8 = load i64, i64* @handler1, align 8
  call void @qthread_start(i64 %8)
  %9 = call i32 @qthread_create(i64* @handler2, i8* (i8*)* @handler_func, i8* null)
  %10 = load i64, i64* @handler2, align 8
  call void @qthread_start(i64 %10)
  store i32 0, i32* %4, align 4
  br label %11

; <label>:11:                                     ; preds = %19, %0
  %12 = load i32, i32* %4, align 4
  %13 = icmp slt i32 %12, 2
  br i1 %13, label %14, label %22

; <label>:14:                                     ; preds = %11
  %15 = load i32, i32* %4, align 4
  %16 = sext i32 %15 to i64
  %17 = getelementptr inbounds [2 x i64], [2 x i64]* %2, i64 0, i64 %16
  %18 = call i32 @pthread_create(i64* %17, %union.pthread_attr_t* null, i8* (i8*)* @th_post1, i8* null) #3
  br label %19

; <label>:19:                                     ; preds = %14
  %20 = load i32, i32* %4, align 4
  %21 = add nsw i32 %20, 1
  store i32 %21, i32* %4, align 4
  br label %11

; <label>:22:                                     ; preds = %11
  store i32 0, i32* %5, align 4
  br label %23

; <label>:23:                                     ; preds = %31, %22
  %24 = load i32, i32* %5, align 4
  %25 = icmp slt i32 %24, 1
  br i1 %25, label %26, label %34

; <label>:26:                                     ; preds = %23
  %27 = load i32, i32* %5, align 4
  %28 = sext i32 %27 to i64
  %29 = getelementptr inbounds [2 x i64], [2 x i64]* %3, i64 0, i64 %28
  %30 = call i32 @pthread_create(i64* %29, %union.pthread_attr_t* null, i8* (i8*)* @th_post2, i8* null) #3
  br label %31

; <label>:31:                                     ; preds = %26
  %32 = load i32, i32* %5, align 4
  %33 = add nsw i32 %32, 1
  store i32 %33, i32* %5, align 4
  br label %23

; <label>:34:                                     ; preds = %23
  store i32 0, i32* %6, align 4
  br label %35

; <label>:35:                                     ; preds = %44, %34
  %36 = load i32, i32* %6, align 4
  %37 = icmp slt i32 %36, 2
  br i1 %37, label %38, label %47

; <label>:38:                                     ; preds = %35
  %39 = load i32, i32* %6, align 4
  %40 = sext i32 %39 to i64
  %41 = getelementptr inbounds [2 x i64], [2 x i64]* %2, i64 0, i64 %40
  %42 = load i64, i64* %41, align 8
  %43 = call i32 @pthread_join(i64 %42, i8** null)
  br label %44

; <label>:44:                                     ; preds = %38
  %45 = load i32, i32* %6, align 4
  %46 = add nsw i32 %45, 1
  store i32 %46, i32* %6, align 4
  br label %35

; <label>:47:                                     ; preds = %35
  %48 = getelementptr inbounds [2 x i64], [2 x i64]* %3, i64 0, i64 0
  %49 = load i64, i64* %48, align 16
  %50 = call i32 @pthread_join(i64 %49, i8** null)
  %51 = load i64, i64* @handler1, align 8
  call void @qthread_wait(i64 %51, i8* null)
  %52 = load i64, i64* @handler2, align 8
  call void @qthread_wait(i64 %52, i8* null)
  %53 = load i32, i32* %1, align 4
  ret i32 %53
}

declare dso_local i32 @qthread_create(i64*, i8* (i8*)*, i8*) #1

declare dso_local void @qthread_start(i64) #1

; Function Attrs: nounwind
declare dso_local i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #2

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 7.0.1-8+deb10u2 (tags/RELEASE_701/final)"}
