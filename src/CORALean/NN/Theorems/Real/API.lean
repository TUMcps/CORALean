module

public import CORALean.NN.Theorems.Real.BucketToleranceNone
public import CORALean.NN.Theorems.Real.InstanceOfInstanceNetwork
public import CORALean.NN.Theorems.Real.LinearConvergent
public import CORALean.NN.Theorems.Real.LinearExact
public import CORALean.NN.Theorems.Real.LinearWithErrorZero
public import CORALean.NN.Theorems.Real.MergeBucketWidth
public import CORALean.NN.Theorems.Real.ReduceOnTheFlyReducesAt

/-!
# What holds of a network only at `𝕋 := ℝ`, collected

Each statement here says more than its generic counterpart, and only because the scalar is ℝ.
`ReduceOnTheFlyReducesAt` puts what [1, Alg. 2] returns in `ReducesAt`, whose networks carry real
biases; `InstanceOfInstanceNetwork` forgets that network, back to the generic `IsInstance`.
`BucketToleranceNone` is [1, Alg. 1] failing to return, which rests on exact subtraction.
`LinearWithErrorZero` is [1, Eq. 2]'s initialization, the box's sum being exact; `LinearExact`
is the linear layer losing nothing at a polynomial zonotope, and `LinearConvergent` what that
makes it in a refinable network. `MergeBucketWidth`/`MergeRowWeightNonneg` bound a bucket and a
merge's cost factor at exact bounds and weights.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/
