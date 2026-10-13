import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Abel

/-!
# Adding a whole set to an evaluated one, [1, (23)]

`plus` lays the two factor blocks side by side, so the summand's factors are
fresh: holding the first operand's factors inside `B` and leaving the second's
free in their box names, in the sum, exactly the evaluated first operand plus
all of the second. That is [1, Def. 4] for `plus`, and it is the step [1]'s
Lemma 4 proof calls (23), without its hypothesis that the summand carry no
dependent factors — with them, they are simply among the free ones.

An enclosure and not an equality only because the free block is quantified on
the right; every point of the left is reached.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, read through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_plus_sum_h {pZ₁ pZ₂ : PolyZonotope α} (f : Fin (pZ₁.h + pZ₂.h) → α) :
    ∑ i : Fin (pZ₁.plus pZ₂).h, f i
      = ∑ i, f (Fin.castAdd pZ₂.h i) + ∑ i, f (Fin.natAdd pZ₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_plus_sum_q {pZ₁ pZ₂ : PolyZonotope α} (f : Fin (pZ₁.q + pZ₂.q) → α) :
    ∑ j : Fin (pZ₁.plus pZ₂).q, f j
      = ∑ j, f (Fin.castAdd pZ₂.q j) + ∑ j, f (Fin.natAdd pZ₁.q j) :=
  Fin.sum_univ_add f

/-- The sum's evaluated point, split along the two blocks the append makes. -/
theorem PolyZonotope.aux_plus_eval (pZ₁ pZ₂ : PolyZonotope α) (a₁ : Fin pZ₁.p → ℝ)
    (a₂ : Fin pZ₂.p → ℝ) (β₁ : Fin pZ₁.q → ℝ) (β₂ : Fin pZ₂.q → ℝ) :
    (pZ₁.plus pZ₂).point (Fin.append a₁ a₂)
        + ∑ j, Fin.append β₁ β₂ j • (pZ₁.plus pZ₂).GI j
      = (pZ₁.point a₁ + ∑ j, β₁ j • pZ₁.GI j)
        + (pZ₂.point a₂ + ∑ j, β₂ j • pZ₂.GI j) := by -- --- PROOF ---
  show pZ₁.c + pZ₂.c + ∑ i : Fin (pZ₁.plus pZ₂).h, _ + ∑ j : Fin (pZ₁.plus pZ₂).q, _ = _
  rw [PolyZonotope.aux_plus_sum_h, PolyZonotope.aux_plus_sum_q]
  simp only [PolyZonotope.plus, PolyZonotope.monomial_plusE_left,
    PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
  show _ = pZ₁.c + ∑ i, _ + _ + (pZ₂.c + ∑ i, _ + _)
  abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the summand adds to an evaluated set is reached by leaving the
summand's own factors free. -/
theorem PolyZonotope.plus_evalOn (pZ₁ pZ₂ : PolyZonotope α) (B : Set (Fin pZ₁.p → ℝ)) :
    pZ₁.evalOn B + pZ₂.construct
      ⊆ (pZ₁.plus pZ₂).evalOn (PolyZonotope.plusBox pZ₁ pZ₂ B) := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a₁, ha₁, β₁, hβ₁, rfl⟩, _, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩, rfl⟩
  refine ⟨Fin.append a₁ a₂, ⟨?_, fun k => ?_⟩, Fin.append β₁ β₂,
    Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j), ?_⟩
  · -- the first block of the appended vector is the original one
    simpa only [Fin.append_left] using ha₁
  · simpa only [Fin.append_right] using ha₂ k
  · exact (PolyZonotope.aux_plus_eval pZ₁ pZ₂ a₁ a₂ β₁ β₂).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
