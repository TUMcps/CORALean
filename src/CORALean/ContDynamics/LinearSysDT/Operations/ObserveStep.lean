module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptions
public import CORALean.ContSet.ContSet.Operations.IntersectStripSeq

@[expose] public section

/-!
# One step of the strip-based observer

[1, Alg. 1]: Step 1 (prediction) `X̄_k = A X̂_{k-1} ⊕ W`, `A p̂ ⊕ [A Ĥ  F]` [1, Eq. 2]; Step 2
(update) the strips `|c_iᵀ x - y_i| ≤ σ_i` met by `intersectStripSeq` [1, Eq. 3] or, as CORA's
`intersectionType = 2` and [3, Alg. 1] do, all at once by `intersectStrip` ([3, Prop. 1]). CORA's
prediction is its `post`, `A X̂ ⊕ B u ⊕ c`, before `W` is added; the papers' systems have neither
input nor offset, `u = 0`, `c = 0`. Written once over the set classes and the scalar: at
`Real.Zonotope` and ℝ it is the paper's step, at `Float.Zonotope` the same step in directed
rounding; soundness for both is `observeStep_outer`. [2, Eq. 4]: the prediction and correction,
steps 1 and 3 of its Sec. 2.1.

## Inputs
* `sys` – system
* `σ` – strip widths
* `W` – disturbance set
* `options` – strip options
* `u` – input at this step
* `y` – measurement at this step
* `Xhat` – previous estimate

## Output
* the next estimate after prediction and update

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21), 2021.
* [3] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotope-based set-membership
      estimation for multi-output uncertain systems". 2013 IEEE International Symposium on
      Intelligent Control (ISIC), 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeStep (sys : LinearSysDT 𝕋 n) (σ : Vec 𝕋 sys.q) (W : S n)
    (options : LinearSysDT.ObserveStripOptions 𝕋 (S n) n sys.q) (u : Vec 𝕋 sys.m) (y : Vec 𝕋 sys.q)
    (Xhat : S n) : S n :=
  let Xbar := plus (plus (plus (mtimes sys.A Xhat) (mtimes sys.B (OfScalarPoint.ofVec u)))
    (OfScalarPoint.ofVec sys.c)) W  -- Step 1, prediction X̄, CORA's `post` then `+ W`
  if options.sequential then intersectStripSeq sys.C σ y options.gain Xbar  -- Step 2, update X̂_k
  else intersectStrip sys.C σ y (options.gain Xbar) Xbar

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
