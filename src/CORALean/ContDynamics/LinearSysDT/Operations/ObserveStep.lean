import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptions
import CORALean.ContSet.ContSet.Operations.IntersectStripSeq

/-!
# One step of the strip-based observer

[1, Alg. 1]: Step 1 (prediction) `X̄_k = A X̂_{k-1} ⊕ W`, which is `A p̂ ⊕ [A Ĥ  F]`
[1, Eq. 2], and Step 2 (update) the measurement strips `|c_iᵀ x - y_i| ≤ σ_i` met by
`intersectStripSeq` [1, Eq. 3], or, as CORA's `intersectionType = 2` does, all at once by
`intersectStrip`. CORA's prediction also adds the known input, `u` here in state coordinates
(`B u` folded, as `LinearSysDT` folds it); the paper's system has none, `u = 0`.

Written once over the set classes and the scalar: at `Real.Zonotope` and ℝ it is the paper's
step, at `Float.Zonotope` and a float type the same step in directed rounding. Soundness, for
both, is `observeStep_outer`.

[2, Eq. 4]: the strip-based observer's prediction and correction, steps 1 and 3 of its Sec. 2.1.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeStep (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n) (σ : Vec 𝕋 p) (W : S n)
    (options : LinearSysDT.ObserveStripOptions 𝕋 (S n) n p) (u : Vec 𝕋 n) (y : Vec 𝕋 p)
    (Xhat : S n) : S n :=
  let Xbar := plus (plus (mtimes sys.A Xhat) (OfScalarPoint.ofVec u)) W  -- Step 1, prediction X̄
  if options.sequential then intersectStripSeq C σ y options.gain Xbar  -- Step 2, update X̂_k
  else intersectStrip C σ y (options.gain Xbar) Xbar

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
