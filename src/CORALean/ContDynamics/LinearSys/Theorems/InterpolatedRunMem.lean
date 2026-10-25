module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormHeldInput
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryHeldInput
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# The interpolated counterexample of [1, Alg. 3 (exits)]

[1]'s Sec. 5.2: once the simplex `P̌ = ⟨[v̌_1 … v̌_{n+1}]⟩_V` of [1, Alg. 3 (exits)] holds the
origin, with `v̌_j = ν(Ř(t), ℓ_j) - ν(L, -ℓ_j)`, the weights `λ_j` of `∑ λ_j v̌_j = 0`, `∑ λ_j = 1`
interpolate the initial states `x_j(0)` and the input sequences `u_j(k)` of the runs reaching the
vertices, and the interpolated run is the counterexample. Here the vertices' runs are any held-input
runs from `R₀` under inputs of `U` and the points `y_j` any points of `L`; [1]'s Eq. (18) is linear
in the initial state and the inputs together, so the interpolated run's state at `t_k` is
`∑ λ_j x_j(k) = ∑ λ_j y_j`, a point of the convex `L`. The weights have to be non-negative, which
[1] leaves to the simplex; a negative weight extrapolates out of `X₀` and `U`.

## Inputs
* `sys` – linear system
* `R₀` – initial set
* `U` – input set
* `Δt` – step length
* `L` – target set
* `ι` – index type of the vertices
* `s` – vertex index set
* `w` – weights
* `x` – vertex start states
* `v` – vertex held inputs
* `y` – target points
* `k` – step index

## Hypotheses
* `hR₀` – initial set convex
* `hUconv` – input set convex
* `hU` – input set bounded
* `hΔt` – step length positive
* `hL` – target set convex
* `hw₀` – weights nonnegative
* `hw₁` – weights sum to one
* `hx` – start states lie in the initial set
* `hv` – held values lie in the input set
* `hy` – target points lie in the target set
* `h0` – weighted state-target differences vanish

## Conclusion
* the interpolated run is a trajectory whose state at the step lies in the target set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1]'s Eq. (18) is linear in the initial state and the inputs together. -/
theorem aux_heldSim_sum (sys : LinearSys 𝕋 n) (Δt : ℝ) {ι : Type} (s : Finset ι) (w : ι → ℝ)
    (x : ι → Vec ℝ n) (v : ι → ℕ → Vec ℝ n) (k : ℕ) : -- --- CONCL ---
    sys.heldSim Δt (∑ j ∈ s, w j • x j) (fun i => ∑ j ∈ s, w j • v j i) k
      = ∑ j ∈ s, w j • sys.heldSim Δt (x j) (v j) k := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show exp (Δt • toRealMat sys.A) *ᵥ sys.heldSim Δt _ _ k
      + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ (∑ j ∈ s, w j • v j k)
      = ∑ j ∈ s, w j • (exp (Δt • toRealMat sys.A) *ᵥ sys.heldSim Δt (x j) (v j) k
        + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ v j k)
    simp only [ih, Matrix.mulVec_sum, Matrix.mulVec_smul, smul_add, Finset.sum_add_distrib]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (exits)]: with convex weights `w_j` (the paper's `λ_j`) and
`∑ w_j (x_j(k) - y_j) = 0`, the run from `∑ w_j x_j` under the held inputs `∑ w_j v_j` is a
`IsTrajectory` whose state at `t_k` lies in `L`. -/
theorem LinearSys.interpolated_run_mem (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (hR₀ : Convex ℝ (construct R₀)) (hUconv : Convex ℝ (construct U))
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt) {L : Set (Vec ℝ n)}
    (hL : Convex ℝ L) {ι : Type} (s : Finset ι) {w : ι → ℝ} (hw₀ : ∀ j ∈ s, 0 ≤ w j)
    (hw₁ : ∑ j ∈ s, w j = 1) {x : ι → Vec ℝ n} (hx : ∀ j ∈ s, x j ∈ construct R₀)
    {v : ι → ℕ → Vec ℝ n} (hv : ∀ j ∈ s, ∀ i, v j i ∈ construct U) {y : ι → Vec ℝ n}
    (hy : ∀ j ∈ s, y j ∈ L) {k : ℕ}
    (h0 : ∑ j ∈ s, w j • (sys.heldSim Δt (x j) (v j) k - y j) = 0) : -- --- CONCL ---
    sys.IsCanonicalTrajectory (Set.Icc 0 (k * Δt)) R₀ U
        (sys.closedForm (∑ j ∈ s, w j • x j)
          (LinearSys.heldInput Δt fun i => ∑ j ∈ s, w j • v j i))
        (LinearSys.heldInput Δt fun i => ∑ j ∈ s, w j • v j i) ∧
      sys.closedForm (∑ j ∈ s, w j • x j)
        (LinearSys.heldInput Δt fun i => ∑ j ∈ s, w j • v j i) (k * Δt) ∈ L := by -- --- PROOF ---
  have hx₀ : ∑ j ∈ s, w j • x j ∈ construct R₀ := hR₀.sum_mem hw₀ hw₁ hx
  have hu : ∀ i, ∑ j ∈ s, w j • v j i ∈ construct U :=
    fun i => hUconv.sum_mem hw₀ hw₁ fun j hj => hv j hj i
  refine ⟨sys.isTrajectory_heldInput R₀ U hU (mul_nonneg k.cast_nonneg hΔt.le) Δt hx₀ hu, ?_⟩
  -- the interpolated state is `∑ w_j x_j(k)`, which `h0` makes `∑ w_j y_j`
  have hsum : ∑ j ∈ s, w j • sys.heldSim Δt (x j) (v j) k = ∑ j ∈ s, w j • y j := by
    simp only [smul_sub, Finset.sum_sub_distrib] at h0
    exact sub_eq_zero.mp h0
  rw [sys.closedForm_heldInput hU hΔt _ hu k, aux_heldSim_sum, hsum]
  exact hL.sum_mem hw₀ hw₁ hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
