module

public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach

@[expose] public section

/-!
# What the input contributes over `ω` steps: one step's contribution per step, carried

`LinearSys.propagateInputSolution_inputReach` read point by point: `y` is in the input reach over
`ω Δt` exactly when it is `Σ_{i<ω} e^{iΔtA} zᵢ` with every `zᵢ` in the input reach over one step.
The support function of the sum along `ℓ` is the sum of the supports along `ℓ e^{iΔtA}`, the
directions CORA's `priv_verifyRA_supportFunc` propagates.

## Inputs
* `sys` – linear system
* `U` – input set
* `Δt` – step length
* `ω` – number of steps
* `y` – vector

## Hypotheses
* `hΔt` – step length nonnegative
* `hbdd` – input set bounded
* `hne` – input set nonempty

## Conclusion
* `y` is in the input reach over `ω Δt` iff it is a carried sum of one-step contributions
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSetLike Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The propagated set, point by point. -/
private theorem LinearSys.aux_mem_propagate_iff (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (Z : Set (Vec ℝ n)) : -- --- CONCL ---
    ∀ (ω : ℕ) (y : Vec ℝ n), y ∈ sys.propagateInputSolution Δt Z ω ↔
      ∃ z : ℕ → Vec ℝ n, (∀ i < ω, z i ∈ Z) ∧
        y = ∑ i ∈ Finset.range ω, exp (((i : ℝ) * Δt) • toRealMat sys.A) *ᵥ z i
        := by -- --- PROOF ---
  intro ω
  induction ω with
  | zero =>
    intro y
    simp only [LinearSys.propagateInputSolution, Set.mem_singleton_iff, Finset.range_zero,
      Finset.sum_empty, not_lt_zero, false_imp_iff, implies_true, true_and, exists_const]
  -- one more step: the last contribution split off the sum
  | succ k ih =>
    intro y
    simp only [LinearSys.propagateInputSolution]
    constructor
    · rintro ⟨a, ha, _, ⟨zk, hzk, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (ih a).mp ha
      refine ⟨Function.update z k zk, fun i hi => ?_, ?_⟩
      · by_cases hik : i = k
        · subst hik; simpa using hzk
        · rw [Function.update_of_ne hik]; exact hz i (by omega)
      · rw [Finset.sum_range_succ, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by simp at hi; omega)]
    -- and back: the sum is the sum before plus the last term
    · rintro ⟨z, hz, rfl⟩
      rw [Finset.sum_range_succ]
      exact Set.add_mem_add ((ih _).mpr ⟨z, fun i hi => hz i (by omega), rfl⟩)
        ⟨z k, hz k (by omega), rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.mem_inputReach_iff_sum (sys : LinearSys 𝕋 n) {U : S n} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (hbdd : Bornology.IsBounded (toSet U)) (hne : (toSet U).Nonempty) (ω : ℕ)
    (y : Vec ℝ n) : -- --- CONCL ---
    y ∈ sys.inputReach U ((ω : ℝ) * Δt) ↔
      ∃ z : ℕ → Vec ℝ n, (∀ i < ω, z i ∈ sys.inputReach U Δt) ∧
        y = ∑ i ∈ Finset.range ω, exp (((i : ℝ) * Δt) • toRealMat sys.A) *ᵥ z i
        := by -- --- PROOF ---
  rw [← sys.propagateInputSolution_inputReach hΔt hbdd hne ω]
  exact sys.aux_mem_propagate_iff Δt _ ω y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
