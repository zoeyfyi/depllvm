define double @foo(double %a, double %b) {
one:
two:
entry:
  ; %foo = phi double [ %a, %entry ]
  ; br label %entry
  ; ret double %entry

  ret double 3.141592653589793
}
; llc test.ll