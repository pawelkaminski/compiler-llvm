@dnl = internal constant [4 x i8] c"%d\0A\00"
@fnl = internal constant [6 x i8] c"%.1f\0A\00"
@d   = internal constant [3 x i8] c"%d\00"	
@lf  = internal constant [4 x i8] c"%lf\00"	
@str = private unnamed_addr constant [3 x i8] c"%s\00", align 1
@.mask = private unnamed_addr constant [3 x i8] c"%s\00", align 1

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare i8* @gets(i8*)
declare noalias i8* @malloc(i32) nounwind
declare i32 @strlen(i8* nocapture) nounwind readonly
declare i8* @strcat(i8*, i8* nocapture) nounwind
declare i8* @strcpy(i8*, i8* nocapture) nounwind
declare i32 @__isoc99_scanf(i8*, ...)

define void @printInt(i32 %x) {
entry: %t0 = getelementptr [4 x i8]* @dnl, i32 0, i32 0
	call i32 (i8*, ...)* @printf(i8* %t0, i32 %x) 
	ret void
}

define void @printString(i8* %s) {
entry:  call i32 @puts(i8* %s)
	ret void
}

define i32 @readInt() {
entry:
	%res = alloca i32
	%t1 = getelementptr [3 x i8]* @d, i32 0, i32 0
	call i32 (i8*, ...)* @scanf(i8* %t1, i32* %res)
	%t2 = load i32* %res
	ret i32 %t2
}


define i8* @readString() {
entry:
  %t = alloca i8*, align 8
  %t1 = call i8* @malloc(i32 256)
  store i8* %t1, i8** %t, align 8
  %t2 = load i8** %t, align 8
  %t3 = call i32 (i8*, ...)* @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8]* @.mask, i32 0, i32 0), i8* %t2)
  %t4 = load i8** %t, align 8
  ret i8* %t4
}

define i8* @concat(i8* %s1, i8* %s2) {
  %1 = call i32 @strlen(i8* %s1)
  %2 = call i32 @strlen(i8* %s2)
  %3 = add i32 %1, 1
  %4 = add i32 %3, %2
  %5 = call i8* @malloc(i32 %4)
  %6 = call i8* @strcpy(i8* %5, i8* %s1)
  %7 = call i8* @strcat(i8* %6, i8* %s2)
  ret i8* %7
}
