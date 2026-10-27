module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBased
public import CORALean.ContDynamics.LinearSysDT.Theorems.ObserveStepOuter

@[expose] public section

/-!
# The strip-based observer holds the true state

CORA's `observe_stripBased`, [1, Alg. 1] run over time: every run `x_{k+1} = A x_k + u_k + ω_k`
from `x_0 ∈ R₀` with `ω_k ∈ W`, whose outputs meet every strip `|C x_k - y_k| ≤ σ`, is in
the observer's set at every step, whatever the gains and the order. Induction on `k`:
`observeStep_outer` at the one state `x_k`, then `reduce_outer`. One statement for every
representation and scalar: at `Real.Zonotope` and ℝ the paper's observer, at `Float.Zonotope`
and a float type the rounded one, with `A`, `u`, `C`, `y`, `σ` the reals the floats store.

[2, Eq. 4], over time: the strip-based observer encloses the true state.

## Inputs
* `sys` – system
* `σ` – strip widths
* `W` – disturbance set
* `R₀` – initial set
* `u` – inputs
* `y` – measurements
* `options` – strip options
* `x` – true states
* `w` – true disturbances
* `k` – step

## Hypotheses
* `h0` – start lies in `R₀`
* `hw` – disturbances lie in `W`
* `hstep` – the dynamics hold
* `hy` – the outputs meet the strips

## Conclusion
* the true state lies in the observer's set at step `k`

## References

* [1] [V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica,
      2013.](../../../../../references/2013/le-automatica-zonotopic-estimation.md)
* [2] [M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21),
      2021.](../../../../../references/2021/althoff-arch-state-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Reduce IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S] [IntersectStrip 𝕋 S] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStripBased_outer (sys : LinearSysDT 𝕋 n) (σ : Vec 𝕋 sys.q)
    (W R₀ : S n) (u : ℕ → Vec 𝕋 sys.m) (y : ℕ → Vec 𝕋 sys.q)
    (options : LinearSysDT.ObserveStripOptions 𝕋 (S n) n sys.q) (x w : ℕ → Vec ℝ n)
    (h0 : x 0 ∈ construct R₀) (hw : ∀ k, w k ∈ construct W)
    (hstep : ∀ k, x (k + 1) =
      toRealMat sys.A *ᵥ x k + toRealMat sys.B *ᵥ toRealVec (u k) + toRealVec sys.c + w k)
    (hy : ∀ k i, |(toRealMat sys.C *ᵥ x k - toRealVec (y k)) i| ≤ toReal (σ i))
    (k : ℕ) : -- --- CONCL ---
    x k ∈ construct (sys.observeStripBased σ W R₀ u y options k) := by -- --- PROOF ---
  induction k with
  | zero =>
    unfold LinearSysDT.observeStripBased
    split
    · exact intersectStripSeq_outer _ _ _ _ _ ⟨h0, hy 0⟩
    · exact intersectStrip_outer _ _ _ _ _ ⟨h0, hy 0⟩
  | succ k ih =>
    unfold LinearSysDT.observeStripBased
    refine reduce_outer _ _ ?_
    refine sys.observeStep_outer σ W options (u k) (y (k + 1)) _
      (Set.singleton_subset_iff.mpr ih) ⟨⟨_, ⟨x k, rfl, rfl⟩, w k, hw k, ?_⟩, hy (k + 1)⟩
    rw [hstep]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
