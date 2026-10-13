module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `padE` changes no monomial

The new factors sit at exponent zero, which is the only reason the block may
be carried through unchanged.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.padE EC r) a l
      = PolyZonotope.monomial EC (fun k => a (Fin.castAdd r k)) l := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  -- the appended factors contribute a product of `1`s
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ ConPolyZono.padE EC r (Fin.natAdd p k) l) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ ConPolyZono.padE EC r (Fin.castAdd r k) l)
      = ∏ k, a (Fin.castAdd r k) ^ EC k l :=
    Finset.prod_congr rfl fun k _ => by
      simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_left]
  rw [hnew, hold, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
