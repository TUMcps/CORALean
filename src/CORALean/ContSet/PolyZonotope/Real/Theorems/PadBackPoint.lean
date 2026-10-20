module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `padBack` moves no point

The padded set at a joint factor vector is the original set at the half of that
vector it was written against. Nothing but the monomials could have changed, and
a factor at exponent zero contributes `a ^ 0 = 1` to every one of them.

Stated over `point` rather than `construct` because that is what a product of
two sets is stated over; the set itself follows, the two constructions differing
in no field a point does not read.

## Inputs
* `r` – number of added factors
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the point ignores the added factors
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The appended factors sit at exponent zero, so each monomial is the one the
original exponent matrix gives at the factors it already had. -/
theorem PolyZonotope.aux_monomial_padBack {p s : ℕ} (E : Fin p → Fin s → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (i : Fin s) : -- --- CONCL ---
    PolyZonotope.monomial (PolyZonotope.padE E r) a i
      = PolyZonotope.monomial E (a ∘ Fin.castAdd r) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  -- the appended half is a product of `1`s
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ PolyZonotope.padE E r (Fin.natAdd p k) i) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ PolyZonotope.padE E r (Fin.castAdd r k) i)
      = ∏ k, (a ∘ Fin.castAdd r) k ^ E k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.padE, Fin.append_left, Function.comp_apply]
  rw [hnew, hold, mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.padBack_point (r : ℕ) (pZ : PolyZonotope α) (a : Fin (pZ.p + r) → ℝ) :
    (pZ.padBack r).point a = pZ.point (a ∘ Fin.castAdd r) := by
  rw [PolyZonotope.point, PolyZonotope.point]
  -- only the exponent matrix differs, and the auxiliary reads it back
  simp only [PolyZonotope.padBack, PolyZonotope.aux_monomial_padBack]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
