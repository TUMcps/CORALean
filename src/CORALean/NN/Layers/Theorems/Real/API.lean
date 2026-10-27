module

public import CORALean.NN.Layers.Theorems.Real.AbsEvalPolyDerivSubCenterLe
public import CORALean.NN.Layers.Theorems.Real.AbsSigmoidDerivLeOne
public import CORALean.NN.Layers.Theorems.Real.AbsSubEvalPolyDerivLe
public import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseH
public import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseHIndep
public import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseQ
public import CORALean.NN.Layers.Theorems.Real.ActivationPolyOnOuter
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
public import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloses
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.BatchNormEncloses
public import CORALean.NN.Layers.Theorems.Real.EvalPolyOne
public import CORALean.NN.Layers.Theorems.Real.EvalPolyScaleCoeffs
public import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst
public import CORALean.NN.Layers.Theorems.Real.ExistsEvalPolyNear
public import CORALean.NN.Layers.Theorems.Real.ExistsFitSamplingErrorLt
public import CORALean.NN.Layers.Theorems.Real.ExistsPolyRelaxationErrorLt
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtEvalPoly
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtTanh
public import CORALean.NN.Layers.Theorems.Real.InvSqrtEqRpow
public import CORALean.NN.Layers.Theorems.Real.InvSqrtLeOne
public import CORALean.NN.Layers.Theorems.Real.InvSqrtRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.OfSamplingError
public import CORALean.NN.Layers.Theorems.Real.OfSamplingEncloses
public import CORALean.NN.Layers.Theorems.Real.PolyDerivDiffOne
public import CORALean.NN.Layers.Theorems.Real.PolyOfAffineConjEncloses
public import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilyEncloses
public import CORALean.NN.Layers.Theorems.Real.RawLeSoftmax
public import CORALean.NN.Layers.Theorems.Real.ReluBoundsOfSlope
public import CORALean.NN.Layers.Theorems.Real.ReluSlopeLeOne
public import CORALean.NN.Layers.Theorems.Real.ReluSlopeNonneg
public import CORALean.NN.Layers.Theorems.Real.SampleBoundsOfDeriv
public import CORALean.NN.Layers.Theorems.Real.SampleGridMemIcc
public import CORALean.NN.Layers.Theorems.Real.SigmoidDerivLoLe
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono
public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilyEncloses
public import CORALean.NN.Layers.Theorems.Real.SigmoidPolyRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.SigmoidRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.SoftmaxEqInv
public import CORALean.NN.Layers.Theorems.Real.SoftmaxLeRaw
public import CORALean.NN.Layers.Theorems.Real.SoftmaxMemTightened
public import CORALean.NN.Layers.Theorems.Real.SoftmaxEncloses
public import CORALean.NN.Layers.Theorems.Real.SubMulBoundsOfDeriv
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
public import CORALean.NN.Layers.Theorems.Real.TanhPolyRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.TanhRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.RootRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.TendstoSamplingError
public import CORALean.NN.Layers.Theorems.Real.SigmoidDerivSShape
public import CORALean.NN.Layers.Theorems.Real.TanhDerivSShape
public import CORALean.NN.Layers.Theorems.Real.DeepZReluEq
public import CORALean.NN.Layers.Theorems.Real.DeepZReluEncloses
public import CORALean.NN.Layers.Theorems.Real.ReluBandAreaLe
public import CORALean.NN.Layers.Theorems.Real.ReluGapOfSlopeEqIte
public import CORALean.NN.Layers.Theorems.Real.SShapeBandSound
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeEncloses
public import CORALean.NN.Layers.Theorems.Real.SShapeBandAreaLe
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeCubeNotEncloses
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeSigmoidEncloses
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeTanhEncloses
public import CORALean.NN.Layers.Theorems.Real.ApproxAreaLe
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorEnclosure
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorIsExtreme
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorRelu
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorSigmoid
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorTanh
public import CORALean.NN.Layers.Theorems.Real.ExistsCriticalExtreme
public import CORALean.NN.Layers.Theorems.Real.EqPmArtanhOfTanh

/-!
# What holds of the standard layers only at ℝ, collected

Facts about the functions over ℝ — sigmoid, tanh, softmax, the inverse square root, a window's
maximum, ReLU's gap, polynomial evaluation — and the exact relaxations built at them:
`EnclosureExactEncloses` and `ScaleRoundingExactEncloses` make the generic constructors exact, and
`SigmoidRelaxationEncloses`, `TanhRelaxationEncloses`, `InvSqrtRelaxationEncloses` and
`SoftmaxSound` follow. The exact polynomial pipeline's sampling error tends to zero
(`TendstoSamplingError`), so a fit within any `ε` exists (`ExistsPolyRelaxationErrorLt`), and
`ActivationPolySound`, `ActivationPolyOnOuter`, `ActivationPolyRefinableConvergent` and
`ActivationPolySigmoidConvergent` are the exact layer's enclosure and convergence.
`ReluSlopeNonneg`/`ReluSlopeLeOne` put the default ReLU slope in `[0, 1]`, which only the exact
order decides; `BatchNormSound` is batch normalization at the fold `Real.sqrt` computes.
`DeepZ*`, `ReluBand*`, `SShapeBand*` and `ReluGapOfSlopeEqIte` are DeepZ's transformers: sound,
of least area, and `DeepZSShapeCubeNotEncloses` unsound for the S-shape its footnote prints.
-/
