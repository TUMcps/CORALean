module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The Taylor truncation lies in the matrix zonotope's Taylor truncation

Induction on the order, the two recursions run in step: `plus_exact` splits off
order `k + 1`, which `Finset.sum_range_succ` splits off the sum, and `map_exact`
scales the power `matPow_outer` places.

The powers are where the dependency is kept — `matPow` carries the cross
generators an interval matrix would have thrown away — and every term is bounded
against the *same* `A`, unlike `expIntervalTaylor`.

## Inputs
* `M` – matrix zonotope
* `A` – member matrix
* `η` – Taylor order

## Hypotheses
* `hA` – member lies in the matrix zonotope

## Conclusion
* the member's Taylor truncation lies in the zonotope's truncation
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One order of the series: the power, scaled, which is `map_exact` at the
scaling and `matPow_outer` at the power. -/
private theorem MatExp.aux_term_mem (M : Zonotope (Mat ℝ n n)) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (i : ℕ) :
    ((Nat.factorial i : ℝ)⁻¹) • A ^ i ∈ (MatExp.expMatZonoTerm M i).construct := by
  rw [MatExp.expMatZonoTerm, ← Zonotope.map_exact]
  exact ⟨A ^ i, Zonotope.matPow_outer M hA i, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expTaylor_mem_expMatZonoTaylor (M : Zonotope (Mat ℝ n n)) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (η : ℕ) : -- --- CONCL ---
    MatExp.expTaylor A η ∈ (MatExp.expMatZonoTaylor M η).construct := by -- --- PROOF ---
  induction η with
  | zero =>
      have h : MatExp.expTaylor A 0 = ((Nat.factorial 0 : ℝ)⁻¹) • A ^ 0 :=
        Finset.sum_range_one _
      rw [h]
      exact MatExp.aux_term_mem M hA 0
  -- the last order split off both the sum and the zonotope, then added back
  | succ k ih =>
      have h : MatExp.expTaylor A (k + 1)
          = ((Nat.factorial (k + 1) : ℝ)⁻¹) • A ^ (k + 1) + MatExp.expTaylor A k := by
        show ∑ i ∈ Finset.range (k + 1 + 1), ((Nat.factorial i : ℝ)⁻¹) • A ^ i = _
        rw [Finset.sum_range_succ]
        exact add_comm _ _
      have hmem := Set.add_mem_add (MatExp.aux_term_mem M hA (k + 1)) ih
      rw [Zonotope.plus_exact] at hmem
      rw [h]
      exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
