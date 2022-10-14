	.section	__TEXT,__text,regular,pure_instructions
	.build_version macos, 12, 0
	.section	__TEXT,__literal8,8byte_literals
	.p2align	3                               ; -- Begin function foo
lCPI0_0:
	.quad	0x400921fb54442d18              ; double 3.1415926535897931
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_foo
	.p2align	2
_foo:                                   ; @foo
	.cfi_startproc
; %bb.0:                                ; %entry
Lloh0:
	adrp	x8, lCPI0_0@PAGE
Lloh1:
	ldr	d0, [x8, lCPI0_0@PAGEOFF]
	ret
	.loh AdrpLdr	Lloh0, Lloh1
	.cfi_endproc
                                        ; -- End function
.subsections_via_symbols
