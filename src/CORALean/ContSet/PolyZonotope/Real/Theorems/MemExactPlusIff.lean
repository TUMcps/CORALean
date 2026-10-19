module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `exactPlus` is the exact addition, independent blocks included

[1, Prop. 10] defines the exact addition `PZ₁ ⊞ PZ₂` of two polynomial zonotopes over a
common identifier vector as the concatenation `⟨[G₁ G₂], [G_{I,1} G_{I,2}], [E₁ E₂], id⟩`,
and its proof reads it as the Minkowski sum `(10)` with the dependent factors shared
instead of renamed apart. This is that reading in full: a point of `exactPlus` is a point
of `pZ₁` plus a point of `pZ₂` at the *same* dependent factors `α` and at independent
factors `β₁`, `β₂` of their own. `exactPlus_point` is the dependent half; the independent
blocks are concatenated, so each operand keeps its own `β`.

The compact operation the proposition applies afterwards merges columns with one exponent
vector and changes the representation, not the set.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The independent block of `exactPlus`, split at the seam into the two operands'. -/
theorem PolyZonotope.aux_sum_indep_exactPlus (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p)
    (β : Fin (pZ₁.q + pZ₂.q) → ℝ) : -- --- STMT ---
    ∑ j : Fin (pZ₁.exactPlus pZ₂ hp).q, β j • (pZ₁.exactPlus pZ₂ hp).GI j
      = ∑ j, β (Fin.castAdd pZ₂.q j) • pZ₁.GI j
        + ∑ j, β (Fin.natAdd pZ₁.q j) • pZ₂.GI j := by -- --- PROOF ---
  show ∑ j : Fin (pZ₁.q + pZ₂.q), β j • Fin.append pZ₁.GI pZ₂.GI j = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10]: `x` lies in the exact addition iff it is a point of `pZ₁` plus a point of
`pZ₂` at one shared dependent factor vector `a` and independent factors of their own. -/
theorem PolyZonotope.mem_exactPlus_iff (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p)
    (x : α) : -- --- STMT ---
    x ∈ (pZ₁.exactPlus pZ₂ hp).construct ↔
      ∃ a : Fin pZ₁.p → ℝ, ∃ β₁ : Fin pZ₁.q → ℝ, ∃ β₂ : Fin pZ₂.q → ℝ,
        (∀ k, |a k| ≤ 1) ∧ (∀ j, |β₁ j| ≤ 1) ∧ (∀ j, |β₂ j| ≤ 1) ∧
        x = (pZ₁.point a + ∑ j, β₁ j • pZ₁.GI j)
          + (pZ₂.point (fun k => a (Fin.cast hp.symm k))
            + ∑ j, β₂ j • pZ₂.GI j) := by -- --- PROOF ---
  -- the dependent part of a member is `exactPlus`'s point, which splits by `exactPlus_point`
  have hpt : ∀ a : Fin pZ₁.p → ℝ,
      (pZ₁.exactPlus pZ₂ hp).c
          + ∑ i, monomial (pZ₁.exactPlus pZ₂ hp).E a i • (pZ₁.exactPlus pZ₂ hp).G i
        = pZ₁.point a + pZ₂.point (fun k => a (Fin.cast hp.symm k)) :=
    fun a => PolyZonotope.exactPlus_point pZ₁ pZ₂ hp a
  constructor
  · rintro ⟨a, β, ha, hβ, rfl⟩
    refine ⟨a, fun j => β (Fin.castAdd pZ₂.q j), fun j => β (Fin.natAdd pZ₁.q j), ha,
      fun j => hβ _, fun j => hβ _, ?_⟩
    rw [hpt a, PolyZonotope.aux_sum_indep_exactPlus]
    abel
  · rintro ⟨a, β₁, β₂, ha, hβ₁, hβ₂, rfl⟩
    -- one independent factor vector, the two operands' side by side
    refine ⟨a, Fin.append β₁ β₂, ha, fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact hβ₁ i
      · rw [Fin.append_right]; exact hβ₂ i
    · rw [hpt a, PolyZonotope.aux_sum_indep_exactPlus]
      simp only [Fin.append_left, Fin.append_right]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
