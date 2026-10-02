import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Abel

/-!
# `PolyZonotope.plus` is exactly the Minkowski sum

The result is [1, Prop. 9].

The witnesses are `Fin.append a₁ a₂` and `Fin.append β₁ β₂` on the factors and
the independent coefficients, and the block-diagonal exponent matrix is what
makes them work: a generator of one set carries exponent zero on every factor of
the other, so its monomial reads back as a monomial of its own set alone.

Exactness is the point of separating the factors. Had the two sets' factors been
identified, the reverse inclusion would fail — one factor cannot take two values
at once, so the sum would come out too small rather than too large.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_plus_h {pZ₁ pZ₂ : PolyZonotope α}
    (f : Fin (pZ₁.h + pZ₂.h) → α) :
    ∑ i : Fin (pZ₁.plus pZ₂).h, f i
      = ∑ i, f (Fin.castAdd pZ₂.h i) + ∑ i, f (Fin.natAdd pZ₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_plus_q {pZ₁ pZ₂ : PolyZonotope α}
    (f : Fin (pZ₁.q + pZ₂.q) → α) :
    ∑ j : Fin (pZ₁.plus pZ₂).q, f j
      = ∑ j, f (Fin.castAdd pZ₂.q j) + ∑ j, f (Fin.natAdd pZ₁.q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.plus_exact (pZ₁ pZ₂ : PolyZonotope α) :
    pZ₁.construct + pZ₂.construct = (pZ₁.plus pZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨a₁, β₁, ha₁, hβ₁, rfl⟩, x₂, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩, rfl⟩
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j), ?_⟩
    rw [PolyZonotope.aux_sum_univ_plus_h, PolyZonotope.aux_sum_univ_plus_q]
    simp only [PolyZonotope.plus, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    abel
  -- back: the appended data split again, giving one point of each set
  · rintro x ⟨a, β, ha, hβ, rfl⟩
    refine ⟨pZ₁.c + ∑ i, PolyZonotope.monomial pZ₁.E (fun k => a (Fin.castAdd pZ₂.p k)) i
              • pZ₁.G i + ∑ j, β (Fin.castAdd pZ₂.q j) • pZ₁.GI j,
            ⟨fun k => a (Fin.castAdd pZ₂.p k), fun j => β (Fin.castAdd pZ₂.q j),
              fun k => ha _, fun j => hβ _, rfl⟩,
            pZ₂.c + ∑ i, PolyZonotope.monomial pZ₂.E (fun k => a (Fin.natAdd pZ₁.p k)) i
              • pZ₂.G i + ∑ j, β (Fin.natAdd pZ₁.q j) • pZ₂.GI j,
            ⟨fun k => a (Fin.natAdd pZ₁.p k), fun j => β (Fin.natAdd pZ₁.q j),
              fun k => ha _, fun j => hβ _, rfl⟩, ?_⟩
    rw [PolyZonotope.aux_sum_univ_plus_h, PolyZonotope.aux_sum_univ_plus_q]
    simp only [PolyZonotope.plus, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
