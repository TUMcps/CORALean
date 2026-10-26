module

public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.BackpropagationFloat
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcos
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcoshFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsin
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtan
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCos
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanCoshFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanExp
public import CORALean.Specification.SyntaxTree.Operations.FunHanExpFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanLog
public import CORALean.Specification.SyntaxTree.Operations.FunHanLogFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinus
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinusFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlusFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPower
public import CORALean.Specification.SyntaxTree.Operations.FunHanPowerFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSin
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrt
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrtFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTan
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanhFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimes
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimesFloat
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.Mtimes
public import CORALean.Specification.SyntaxTree.Operations.MtimesFloat
public import CORALean.Specification.SyntaxTree.Operations.Nthroot
public import CORALean.Specification.SyntaxTree.Operations.NthrootFloat
public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.Operations.NthrootZFloat
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.Operations.PeriodicFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat
public import CORALean.Specification.SyntaxTree.Operations.Restrict
public import CORALean.Specification.SyntaxTree.Operations.SignedRoots
public import CORALean.Specification.SyntaxTree.Operations.SignedRootsFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat

/-!
# Syntax trees: the operations

The methods of `syntaxTree.m`: a constructor for each operator (`power`, `exp`, ..., `plus`,
`times`,
with a numeric operand variant of the binary ones), `sum`, `prod`, `mtimes` and `backpropagation`;
the
`funHan` of each node is its `aux_` function. `sinhCora` and `tanCora` are the nodes with the
`funHan` as
printed, which is not sound.
-/
