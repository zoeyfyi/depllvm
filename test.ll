define double @foo(double %a, double %b) {
entry:
  %foo = phi double [ %a, %entry ]
  br label %entry
  ; ret double 3.141592653589793
}
