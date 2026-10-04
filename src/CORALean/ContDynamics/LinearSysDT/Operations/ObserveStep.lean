import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptions
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
import CORALean.ContSet.Zonotope.Real.Operations.IntersectStripSeq

/-!
# One step of the strip-based observer

[1, Alg. 1]: Step 1 (prediction) `X̄_k = A X̂_{k-1} ⊕ W`, which is `A p̂ ⊕ [A Ĥ  F]`
[1, Eq. 2], and Step 2 (update) the measurement strips `|c_iᵀ x - y_i| ≤ σ_i` met by
`intersectStripSeq` [1, Eq. 3], or, as CORA's `intersectionType = 2` does, all at once by
`intersectStrip`. CORA's prediction also adds the known input, `u` here in state coordinates
(`B u` folded, as `LinearSysDT` folds it); the paper's system has none, `u = 0`.

[2, Eq. 4]: the strip-based observer's prediction and correction, steps 1 and 3 of its Sec. 2.1.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeStep (sys : LinearSysDT ℝ n) (C : Mat ℝ p n) (σ : Vec ℝ p)
    (W : Zonotope (Vec ℝ n)) (options : LinearSysDT.ObserveStripOptions n p) (u : Vec ℝ n)
    (y : Vec ℝ p) (Xhat : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let Xbar := ((Xhat.mtimes sys.A).plus (Zonotope.ofPoint u)).plus W  -- Step 1, prediction X̄
  if options.sequential then Xbar.intersectStripSeq C σ y options.gain  -- Step 2, update X̂_k
  else Xbar.intersectStrip C σ y (options.gain Xbar)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
