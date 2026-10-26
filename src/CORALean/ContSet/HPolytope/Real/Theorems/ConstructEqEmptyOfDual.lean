module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `HPolytope.construct_eq_empty_of_dual`

Weights that cancel the objective but not the right-hand side prove the
description denotes nothing — the certificate of infeasibility an LP solver
returns instead of a solution.

## Inputs
* `P` – H-polytope
* `y` – real numbers indexed by `Fin P.m`
* `z` – real numbers indexed by `Fin P.me`

## Hypotheses
* `hy` – `∀ i, 0 ≤ y i`
* `h0` – the weighted rows sum to zero
* `hneg` – the weighted bounds sum to a negative number

## Conclusion
* `P.construct = ∅`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type} [AddCommGroup α] [Module ℝ α] {m me : ℕ}

/-- Farkas: weights that cancel the objective but not the right-hand side leave
no feasible point at all. -/
private theorem _root_.CORALean.aux_eq_empty_of_dual {A : Fin m → (α →ₗ[ℝ] ℝ)} {b : Fin m → ℝ}
    {Ae : Fin me → (α →ₗ[ℝ] ℝ)} {be : Fin me → ℝ}
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (h0 : ∀ x : α, (∑ i, y i * A i x) + ∑ i, z i * Ae i x = 0)
    (hneg : (∑ i, y i * b i) + ∑ i, z i * be i < 0) : -- --- CONCL ---
    Feasible A b Ae be = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hle, heq⟩
  have h := le_dual_bound A b Ae be y z hy hle heq
  rw [h0 x] at h
  linarith

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- Weights that cancel the objective but not the right-hand side prove the
description denotes nothing — the certificate of infeasibility an LP solver
returns instead of a solution. -/
theorem HPolytope.construct_eq_empty_of_dual (P : HPolytope α)
    (y : Fin P.m → ℝ) (z : Fin P.me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (h0 : ∀ x : α, (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x = 0)
    (hneg : (∑ i, y i * P.b i) + ∑ i, z i * P.be i < 0) : -- --- CONCL ---
    P.construct = ∅ := by -- --- PROOF ---
  rw [P.construct_eq_feasible]
  exact aux_eq_empty_of_dual y z hy h0 hneg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
