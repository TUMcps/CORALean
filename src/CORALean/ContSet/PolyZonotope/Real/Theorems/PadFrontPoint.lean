import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import Mathlib.Algebra.BigOperators.Fin

/-!
# `padFront` moves no point

`padBack_point` from the other side: the padded set at a joint factor vector is
the original at the second half of it, the prepended factors again standing at
exponent zero in every monomial.

The two halves together are what a product over independent factors is read
through, one set per projection out of `Fin (p₁ + p₂)`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The prepended factors sit at exponent zero, so each monomial is the one the
original exponent matrix gives at the factors it already had. -/
theorem PolyZonotope.aux_monomial_padFront {p s : ℕ} (l : ℕ) (E : Fin p → Fin s → ℕ)
    (a : Fin (l + p) → ℝ) (i : Fin s) :
    PolyZonotope.monomial (PolyZonotope.padFrontE l E) a i
      = PolyZonotope.monomial E (a ∘ Fin.natAdd l) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  -- the prepended half is a product of `1`s
  have hnew : (∏ k : Fin l, a (Fin.castAdd p k)
      ^ PolyZonotope.padFrontE l E (Fin.castAdd p k) i) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.padFrontE, Fin.append_left, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.natAdd l k)
      ^ PolyZonotope.padFrontE l E (Fin.natAdd l k) i)
      = ∏ k, (a ∘ Fin.natAdd l) k ^ E k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.padFrontE, Fin.append_right, Function.comp_apply]
  rw [hnew, hold, one_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.padFront_point (l : ℕ) (pZ : PolyZonotope α) (a : Fin (l + pZ.p) → ℝ) :
    (pZ.padFront l).point a = pZ.point (a ∘ Fin.natAdd l) := by
  rw [PolyZonotope.point, PolyZonotope.point]
  -- only the exponent matrix differs, and the auxiliary reads it back
  simp only [PolyZonotope.padFront, PolyZonotope.aux_monomial_padFront]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
