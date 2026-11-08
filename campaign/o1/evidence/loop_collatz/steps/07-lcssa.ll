; ModuleID = '<stdin>'
source_filename = "<stdin>"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f(i32 noundef %n) local_unnamed_addr {
entry:
  %c1 = icmp ult i32 %n, 2
  br i1 %c1, label %done, label %b.preheader

b.preheader:                                      ; preds = %entry
  br label %b

b:                                                ; preds = %b.preheader, %b
  %k3 = phi i32 [ %k1, %b ], [ 0, %b.preheader ]
  %x2 = phi i32 [ %y, %b ], [ %n, %b.preheader ]
  %odd = and i32 %x2, 1
  %isodd.not = icmp eq i32 %odd, 0
  %t3 = mul i32 %x2, 3
  %t31 = add i32 %t3, 1
  %half = lshr i32 %x2, 1
  %y = select i1 %isodd.not, i32 %half, i32 %t31
  %k1 = add i32 %k3, 1
  %c = icmp ult i32 %y, 2
  br i1 %c, label %done.loopexit, label %b

done.loopexit:                                    ; preds = %b
  %k1.lcssa = phi i32 [ %k1, %b ]
  br label %done

done:                                             ; preds = %done.loopexit, %entry
  %k.lcssa = phi i32 [ 0, %entry ], [ %k1.lcssa, %done.loopexit ]
  ret i32 %k.lcssa
}
