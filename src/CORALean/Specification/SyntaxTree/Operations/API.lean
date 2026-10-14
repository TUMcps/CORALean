module

public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcos
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsin
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtan
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanCos
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosh
public import CORALean.Specification.SyntaxTree.Operations.FunHanExp
public import CORALean.Specification.SyntaxTree.Operations.FunHanLog
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlus
public import CORALean.Specification.SyntaxTree.Operations.FunHanPower
public import CORALean.Specification.SyntaxTree.Operations.FunHanSin
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinh
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinhCora
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrt
public import CORALean.Specification.SyntaxTree.Operations.FunHanTan
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanCora
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimes
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Mtimes
public import CORALean.Specification.SyntaxTree.Operations.Nthroot
public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.Operations.Restrict
public import CORALean.Specification.SyntaxTree.Operations.SignedRoots

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
