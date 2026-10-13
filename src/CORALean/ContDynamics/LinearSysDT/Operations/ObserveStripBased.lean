import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep

/-!
# The strip-based observer

CORA's `observe_stripBased`, the loop of [1, Alg. 1]: the initial set `R₀` met with the first
measurement's strips, then at every step the prediction and update of `observeStep` followed
by `reduce` to `ρ` ([1, Prop. 3] is one such reduction). The strip widths are
CORA's `sigma = supremum(abs(interval(params.V)))`, here `σ`, so a noise `v ∈ V` needs only
`|vᵢ| ≤ σᵢ`. CORA's estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A` are
this loop at their own gains; `observeStripBased_outer` holds for every gain.

Written once over the set classes and the scalar: at `Real.Zonotope` and ℝ it is the paper's
loop, at `Float.Zonotope` and a float type the same loop in directed rounding, and
`observeStripBased_outer` is the soundness of both.

[2, Eq. 4], over time.

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

open ContSet Reduce IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S] [IntersectStrip 𝕋 S] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R k`, the set the observer holds after the measurement `y k`. -/
def LinearSysDT.observeStripBased (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n) (σ : Vec 𝕋 p)
    (W R₀ : S n) (u : ℕ → Vec 𝕋 n) (y : ℕ → Vec 𝕋 p)
    (options : LinearSysDT.ObserveStripOptions 𝕋 (S n) n p) : ℕ → S n
  | 0 =>
    if options.sequential then intersectStripSeq C σ (y 0) options.gain R₀
    else intersectStrip C σ (y 0) (options.gain R₀) R₀
  | k + 1 =>
    reduce (sys.observeStep C σ W options (u k) (y (k + 1))
      (sys.observeStripBased C σ W R₀ u y options k)) options.ρ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
