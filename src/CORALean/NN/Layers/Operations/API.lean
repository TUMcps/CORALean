import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.ActivationLayerOf
import CORALean.NN.Layers.Operations.ActivationPoly
import CORALean.NN.Layers.Operations.ActivationPolyRefinable
import CORALean.NN.Layers.Operations.AllOver
import CORALean.NN.Layers.Operations.AvgPool
import CORALean.NN.Layers.Operations.BatchNorm
import CORALean.NN.Layers.Operations.BracketError
import CORALean.NN.Layers.Operations.BracketShift
import CORALean.NN.Layers.Operations.ClampUnit
import CORALean.NN.Layers.Operations.CoarseHi
import CORALean.NN.Layers.Operations.CoarseLo
import CORALean.NN.Layers.Operations.ConjError
import CORALean.NN.Layers.Operations.ConjOffset
import CORALean.NN.Layers.Operations.ConjOffsetGap
import CORALean.NN.Layers.Operations.ConjOffsetHigh
import CORALean.NN.Layers.Operations.ConjOffsetLow
import CORALean.NN.Layers.Operations.ConjSlope
import CORALean.NN.Layers.Operations.ConjSlopeGap
import CORALean.NN.Layers.Operations.ConjSlopeHigh
import CORALean.NN.Layers.Operations.ConjSlopeLow
import CORALean.NN.Layers.Operations.ConjTBound
import CORALean.NN.Layers.Operations.Conv
import CORALean.NN.Layers.Operations.CurvHi
import CORALean.NN.Layers.Operations.CurvLo
import CORALean.NN.Layers.Operations.CurvMid
import CORALean.NN.Layers.Operations.DoubleRounding
import CORALean.NN.Layers.Operations.ElementwiseAffine
import CORALean.NN.Layers.Operations.LipConstrLinear
import CORALean.NN.Layers.Operations.LipConstrScale
import CORALean.NN.Layers.Operations.EnclosureMid
import CORALean.NN.Layers.Operations.EvalPolyDown
import CORALean.NN.Layers.Operations.EvalPolyUp
import CORALean.NN.Layers.Operations.Exp
import CORALean.NN.Layers.Operations.ExpEnclosure
import CORALean.NN.Layers.Operations.ExpRelaxation
import CORALean.NN.Layers.Operations.FitHi
import CORALean.NN.Layers.Operations.FitLo
import CORALean.NN.Layers.Operations.GeneratorReduction
import CORALean.NN.Layers.Operations.GridChecked
import CORALean.NN.Layers.Operations.LayerRelaxationBox
import CORALean.NN.Layers.Operations.LayerRelaxationCoeffList
import CORALean.NN.Layers.Operations.LayerRelaxationCoeffVec
import CORALean.NN.Layers.Operations.LeakyRelu
import CORALean.NN.Layers.Operations.LeakyReluEndUp
import CORALean.NN.Layers.Operations.LeakyReluGapUp
import CORALean.NN.Layers.Operations.LeakyReluRelaxation
import CORALean.NN.Layers.Operations.LeakyReluSlope
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.LinearWithError
import CORALean.NN.Layers.Operations.MaxPool
import CORALean.NN.Layers.Operations.MaxPoolGapUp
import CORALean.NN.Layers.Operations.MulRangeDown
import CORALean.NN.Layers.Operations.MulRangeUp
import CORALean.NN.Layers.Operations.OnePlusExpDown
import CORALean.NN.Layers.Operations.Pack
import CORALean.NN.Layers.Operations.PadCoeffs
import CORALean.NN.Layers.Operations.PolyDerivBoundUp
import CORALean.NN.Layers.Operations.PolyDerivCenter
import CORALean.NN.Layers.Operations.PolyDerivRadiusUp
import CORALean.NN.Layers.Operations.PolyRelaxationFamilyAtPattern
import CORALean.NN.Layers.Operations.PolyRelaxationFamilyDegOf
import CORALean.NN.Layers.Operations.PolyRelaxationOfBracket
import CORALean.NN.Layers.Operations.PolyRelaxationOfSampling
import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
import CORALean.NN.Layers.Operations.PolyRelaxationToRelaxation
import CORALean.NN.Layers.Operations.PowRange
import CORALean.NN.Layers.Operations.RelaxationBox
import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
import CORALean.NN.Layers.Operations.RelaxationOfAntitone
import CORALean.NN.Layers.Operations.RelaxationOfDeriv
import CORALean.NN.Layers.Operations.RelaxationOfMonotone
import CORALean.NN.Layers.Operations.RelaxationSlopeMat
import CORALean.NN.Layers.Operations.RelaxationTighter
import CORALean.NN.Layers.Operations.RelaxationToPoly
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.ReluGapUp
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Operations.Reshape
import CORALean.NN.Layers.Operations.SampleDevLo
import CORALean.NN.Layers.Operations.SampleDevUp
import CORALean.NN.Layers.Operations.SampleHi
import CORALean.NN.Layers.Operations.SampleLo
import CORALean.NN.Layers.Operations.SelectMat
import CORALean.NN.Layers.Operations.ShiftConst
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Operations.SigmoidCurvatureRelaxation
import CORALean.NN.Layers.Operations.SigmoidDerivHi
import CORALean.NN.Layers.Operations.SigmoidDerivLo
import CORALean.NN.Layers.Operations.SigmoidEnclosure
import CORALean.NN.Layers.Operations.SigmoidPoly
import CORALean.NN.Layers.Operations.SigmoidPolyDerivBound
import CORALean.NN.Layers.Operations.SigmoidPolyRelaxation
import CORALean.NN.Layers.Operations.SigmoidRelaxation
import CORALean.NN.Layers.Operations.SigmoidSlope
import CORALean.NN.Layers.Operations.Softmax
import CORALean.NN.Layers.Operations.SoftmaxBox
import CORALean.NN.Layers.Operations.SoftmaxDenomDown
import CORALean.NN.Layers.Operations.SoftmaxRawUpper
import CORALean.NN.Layers.Operations.Softplus
import CORALean.NN.Layers.Operations.SoftplusEnclosure
import CORALean.NN.Layers.Operations.SoftplusRelaxation
import CORALean.NN.Layers.Operations.Square
import CORALean.NN.Layers.Operations.SquareDerivHi
import CORALean.NN.Layers.Operations.SquareDerivLo
import CORALean.NN.Layers.Operations.SquareEnclosure
import CORALean.NN.Layers.Operations.SquareRelaxation
import CORALean.NN.Layers.Operations.SquareSlope
import CORALean.NN.Layers.Operations.SumOffDown
import CORALean.NN.Layers.Operations.SumOffUp
import CORALean.NN.Layers.Operations.Tanh
import CORALean.NN.Layers.Operations.TanhRelaxation
import CORALean.NN.Layers.Operations.Root
import CORALean.NN.Layers.Operations.RootEnclosure
import CORALean.NN.Layers.Operations.RootRelaxation
import CORALean.NN.Layers.Operations.InvSqrtRoot
import CORALean.NN.Layers.Operations.InvSqrtRootEnclosure
import CORALean.NN.Layers.Operations.InvSqrtRootRelaxation
import CORALean.NN.Layers.Operations.TapEntry
import CORALean.NN.Layers.Operations.TapMat
import CORALean.NN.Layers.Operations.TransposeEquiv

/-!
# The standard layers, collected

Each written once over the scalar, and each a `Layer` the network holds.

**Linear in disguise.** `Linear`, and then `Conv` at a stencil (`TapEntry`, `TapMat`), `AvgPool`
and `BatchNorm`: each is `Layer.linear` at a particular matrix, by definition, the matrix placed
rather than summed so that nothing rounds. `LinearWithError` carries an error box.

**Relaxations.** `Activation` at a `Relaxation`, whose `RelaxationBox` is the one place it
rounds and `RelaxationSlopeMat` the affine part. The constructors: `RelaxationOfMonotone` and
`RelaxationOfAntitone` from an enclosure's ends (`EnclosureMid`), `RelaxationOfDeriv` from a
derivative bracket (`CurvLo`, `CurvHi`, `CurvMid`), `RelaxationTighter` keeping the better of
two, and `RelaxationOfAffineConj` transporting one through `t ↦ a f (b t) + c` (the `Conj*`
pieces). `Relu`, `Sigmoid` and `Tanh` are layers built from them; `Softmax` needs its own box.

**Polynomials.** `ActivationPoly` evaluates a fit per neuron on a polynomial zonotope and
`ActivationPolyRefinable` is it with an order still to choose. A fit comes from
`PolyRelaxationOfSampling` (checked on a grid, `Sample*`, `Coarse*`, `Fit*`) or
`PolyRelaxationOfBracket`, is lifted by `PolyRelaxationPadTo`, and `SigmoidPoly` is the sigmoid's.

**Neither.** `Reshape` relabels (`TransposeEquiv`), exactly. `MaxPool` encloses through
`SelectMat` and a gap `MaxPoolGapUp`, its output depending on a window and not a coordinate.
-/
