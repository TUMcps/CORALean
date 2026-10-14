module

public import CORALean.Specification.SyntaxTree.Theorems.AuxSignedSpec
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationBinaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationSound
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationUnaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationVarOk
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage
public import CORALean.Specification.SyntaxTree.Theorems.ContainsTimes
public import CORALean.Specification.SyntaxTree.Theorems.CosSound
public import CORALean.Specification.SyntaxTree.Theorems.CoshSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAcos
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAcosh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAsin
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAsinh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAtan
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesAtanh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesCos
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesCosh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesExp
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesLog
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesPower
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSin
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSinh
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSinhCora
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesSqrt
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesTan
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesTanCora
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesTanh
public import CORALean.Specification.SyntaxTree.Theorems.EvalMtimes
public import CORALean.Specification.SyntaxTree.Theorems.EvalProd
public import CORALean.Specification.SyntaxTree.Theorems.EvalSinhCora
public import CORALean.Specification.SyntaxTree.Theorems.EvalSum
public import CORALean.Specification.SyntaxTree.Theorems.EvalTanCora
public import CORALean.Specification.SyntaxTree.Theorems.ExpSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcosSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAcoshSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAsinhSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanAtanhSound
public import CORALean.Specification.SyntaxTree.Theorems.FunHanSinhSound
public import CORALean.Specification.SyntaxTree.Theorems.LogSound
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains
public import CORALean.Specification.SyntaxTree.Theorems.MinusSound
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicContains
public import CORALean.Specification.SyntaxTree.Theorems.PlusSound
public import CORALean.Specification.SyntaxTree.Theorems.PowerSound
public import CORALean.Specification.SyntaxTree.Theorems.RestrictContains
public import CORALean.Specification.SyntaxTree.Theorems.SinSound
public import CORALean.Specification.SyntaxTree.Theorems.SinhCoraCounterexample
public import CORALean.Specification.SyntaxTree.Theorems.SoundAcos
public import CORALean.Specification.SyntaxTree.Theorems.SoundAcosh
public import CORALean.Specification.SyntaxTree.Theorems.SoundAsin
public import CORALean.Specification.SyntaxTree.Theorems.SoundAsinh
public import CORALean.Specification.SyntaxTree.Theorems.SoundAtan
public import CORALean.Specification.SyntaxTree.Theorems.SoundAtanh
public import CORALean.Specification.SyntaxTree.Theorems.SoundCos
public import CORALean.Specification.SyntaxTree.Theorems.SoundCosh
public import CORALean.Specification.SyntaxTree.Theorems.SoundExp
public import CORALean.Specification.SyntaxTree.Theorems.SoundLog
public import CORALean.Specification.SyntaxTree.Theorems.SoundMtimes
public import CORALean.Specification.SyntaxTree.Theorems.SoundProd
public import CORALean.Specification.SyntaxTree.Theorems.SoundSin
public import CORALean.Specification.SyntaxTree.Theorems.SoundSinh
public import CORALean.Specification.SyntaxTree.Theorems.SoundSqrt
public import CORALean.Specification.SyntaxTree.Theorems.SoundSum
public import CORALean.Specification.SyntaxTree.Theorems.SoundTan
public import CORALean.Specification.SyntaxTree.Theorems.SoundTanh
public import CORALean.Specification.SyntaxTree.Theorems.SqrtSound
public import CORALean.Specification.SyntaxTree.Theorems.TanCoraCounterexample
public import CORALean.Specification.SyntaxTree.Theorems.TanSound
public import CORALean.Specification.SyntaxTree.Theorems.TanhSound
public import CORALean.Specification.SyntaxTree.Theorems.TimesSound
public import CORALean.Specification.SyntaxTree.Theorems.UminusSound

/-!
# Syntax trees: the theorems

`eval_*` say what each constructor denotes. The `encloses_*` theorems say its stored interval
encloses
that function, the `*_sound` theorems that its `funHan` is sound, `sound_*` that a constructor
keeps a
tree `Sound`, and `backpropagation_sound` that `backpropagation` of a sound tree keeps every
solution.
`sinhCora_counterexample` and `tanCora_counterexample` are the two places CORA's `funHan` is not
sound.
-/
