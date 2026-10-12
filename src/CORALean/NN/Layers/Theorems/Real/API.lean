import CORALean.NN.Layers.Theorems.Real.AbsEvalPolyDerivSubCenterLe
import CORALean.NN.Layers.Theorems.Real.AbsSigmoidDerivLeOne
import CORALean.NN.Layers.Theorems.Real.AbsSubEvalPolyDerivLe
import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseH
import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseHIndep
import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseQ
import CORALean.NN.Layers.Theorems.Real.ActivationPolyOnOuter
import CORALean.NN.Layers.Theorems.Real.ActivationPolyRefinableConvergent
import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
import CORALean.NN.Layers.Theorems.Real.ActivationPolySound
import CORALean.NN.Layers.Theorems.Real.ActivationPolySubsetInflate
import CORALean.NN.Layers.Theorems.Real.AntitoneInvSqrt
import CORALean.NN.Layers.Theorems.Real.BatchNormSound
import CORALean.NN.Layers.Theorems.Real.ContinuousInvSqrt
import CORALean.NN.Layers.Theorems.Real.EnclosureExactSound
import CORALean.NN.Layers.Theorems.Real.EvalPolyCoeff
import CORALean.NN.Layers.Theorems.Real.EvalPolyOne
import CORALean.NN.Layers.Theorems.Real.EvalPolyPadCoeffs
import CORALean.NN.Layers.Theorems.Real.EvalPolyScaleCoeffs
import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst
import CORALean.NN.Layers.Theorems.Real.ExistsEvalPolyNear
import CORALean.NN.Layers.Theorems.Real.ExistsFitSamplingErrorLt
import CORALean.NN.Layers.Theorems.Real.ExistsPolyRelaxationErrorLt
import CORALean.NN.Layers.Theorems.Real.ExistsSampleGridClose
import CORALean.NN.Layers.Theorems.Real.ExpSumPos
import CORALean.NN.Layers.Theorems.Real.HasDerivAtEvalPoly
import CORALean.NN.Layers.Theorems.Real.HasDerivAtInvSqrt
import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
import CORALean.NN.Layers.Theorems.Real.HasDerivAtTanh
import CORALean.NN.Layers.Theorems.Real.InvSqrtDerivMono
import CORALean.NN.Layers.Theorems.Real.InvSqrtEqOfOneLe
import CORALean.NN.Layers.Theorems.Real.InvSqrtEqRpow
import CORALean.NN.Layers.Theorems.Real.InvSqrtLeOne
import CORALean.NN.Layers.Theorems.Real.InvSqrtPos
import CORALean.NN.Layers.Theorems.Real.InvSqrtRelaxationSound
import CORALean.NN.Layers.Theorems.Real.LeSigmoidDerivHi
import CORALean.NN.Layers.Theorems.Real.LeWindowMax
import CORALean.NN.Layers.Theorems.Real.LeakyReluBoundsOfSlope
import CORALean.NN.Layers.Theorems.Real.MaxPoolBounds
import CORALean.NN.Layers.Theorems.Real.OfSamplingError
import CORALean.NN.Layers.Theorems.Real.OfSamplingSound
import CORALean.NN.Layers.Theorems.Real.PolyDerivDiffOne
import CORALean.NN.Layers.Theorems.Real.PolyOfAffineConjSound
import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilyErrorLt
import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilySound
import CORALean.NN.Layers.Theorems.Real.RawLeSoftmax
import CORALean.NN.Layers.Theorems.Real.ReluBoundsOfSlope
import CORALean.NN.Layers.Theorems.Real.ReluSlopeLeOne
import CORALean.NN.Layers.Theorems.Real.ReluSlopeNonneg
import CORALean.NN.Layers.Theorems.Real.SampleBoundsOfDeriv
import CORALean.NN.Layers.Theorems.Real.SampleGridMemIcc
import CORALean.NN.Layers.Theorems.Real.SamplingErrorBracket
import CORALean.NN.Layers.Theorems.Real.ScaleRoundingExactSound
import CORALean.NN.Layers.Theorems.Real.SigmoidDerivLoLe
import CORALean.NN.Layers.Theorems.Real.SigmoidLtOne
import CORALean.NN.Layers.Theorems.Real.SigmoidMono
import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyFamilySound
import CORALean.NN.Layers.Theorems.Real.SigmoidPolyRelaxationSound
import CORALean.NN.Layers.Theorems.Real.SigmoidPos
import CORALean.NN.Layers.Theorems.Real.SigmoidRelaxationSound
import CORALean.NN.Layers.Theorems.Real.SoftmaxEqInv
import CORALean.NN.Layers.Theorems.Real.SoftmaxLeRaw
import CORALean.NN.Layers.Theorems.Real.SoftmaxMemTightened
import CORALean.NN.Layers.Theorems.Real.SoftmaxNonneg
import CORALean.NN.Layers.Theorems.Real.SoftmaxSound
import CORALean.NN.Layers.Theorems.Real.SoftmaxSumEqOne
import CORALean.NN.Layers.Theorems.Real.SoftplusMono
import CORALean.NN.Layers.Theorems.Real.SubMulBoundsOfDeriv
import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
import CORALean.NN.Layers.Theorems.Real.TanhPolyRelaxationSound
import CORALean.NN.Layers.Theorems.Real.TanhRelaxationSound
import CORALean.NN.Layers.Theorems.Real.RootRelaxationSound
import CORALean.NN.Layers.Theorems.Real.TendstoSamplingError
import CORALean.NN.Layers.Theorems.Real.WindowMaxLe
import CORALean.NN.Layers.Theorems.Real.SigmoidDerivSShape
import CORALean.NN.Layers.Theorems.Real.TanhDerivSShape
import CORALean.NN.Layers.Theorems.Real.DeepZReluEq
import CORALean.NN.Layers.Theorems.Real.DeepZReluSound
import CORALean.NN.Layers.Theorems.Real.ReluBandAreaLe
import CORALean.NN.Layers.Theorems.Real.ReluGapOfSlopeEqIte
import CORALean.NN.Layers.Theorems.Real.SShapeBandSound
import CORALean.NN.Layers.Theorems.Real.DeepZSShapeSound
import CORALean.NN.Layers.Theorems.Real.SShapeBandAreaLe
import CORALean.NN.Layers.Theorems.Real.EvaluateSinghCoraMissesCounterexample
import CORALean.NN.Layers.Theorems.Real.DeepZSShapeCubeNotSound
import CORALean.NN.Layers.Theorems.Real.DeepZSShapeSigmoidSound
import CORALean.NN.Layers.Theorems.Real.DeepZSShapeTanhSound
import CORALean.NN.Layers.Theorems.Real.ApproxAreaLe
import CORALean.NN.Layers.Theorems.Real.ApproxErrorEnclosure
import CORALean.NN.Layers.Theorems.Real.ApproxErrorIsExtreme
import CORALean.NN.Layers.Theorems.Real.ApproxErrorRelaxationSound
import CORALean.NN.Layers.Theorems.Real.ApproxErrorRelu
import CORALean.NN.Layers.Theorems.Real.ApproxErrorSigmoid
import CORALean.NN.Layers.Theorems.Real.ApproxErrorTanh
import CORALean.NN.Layers.Theorems.Real.ExistsCriticalExtreme
import CORALean.NN.Layers.Theorems.Real.EqPmArtanhOfTanh
import CORALean.NN.Layers.Theorems.Real.EncloseNonlinearPrintedCounterexample

/-!
# What holds of the standard layers only at ℝ, collected

Facts about the functions over ℝ — sigmoid, tanh, softmax, the inverse square root, a window's
maximum, ReLU's gap, polynomial evaluation — and the exact relaxations built at them:
`EnclosureExactSound` and `ScaleRoundingExactSound` make the generic constructors exact, and
`SigmoidRelaxationSound`, `TanhRelaxationSound`, `InvSqrtRelaxationSound` and `SoftmaxSound`
follow. The exact polynomial pipeline's sampling error tends to zero (`TendstoSamplingError`),
so a fit within any `ε` exists (`ExistsPolyRelaxationErrorLt`), and `ActivationPolySound`,
`ActivationPolyOnOuter`, `ActivationPolyRefinableConvergent` and
`ActivationPolySigmoidConvergent` are the exact layer's enclosure and convergence.
`ReluSlopeNonneg`/`ReluSlopeLeOne` put the default ReLU slope in `[0, 1]`, which only the exact
order decides; `BatchNormSound` is batch normalization at the fold `Real.sqrt` computes.
`DeepZ*`, `ReluBand*`, `SShapeBand*` and `ReluGapOfSlopeEqIte` are DeepZ's transformers: sound,
of least area, and `DeepZSShapeCubeNotSound` unsound for the S-shape its footnote prints.
-/
