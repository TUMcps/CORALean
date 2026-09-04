import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.padE`

An exponent matrix widened by fresh factors that none of its monomials uses:
what a constraint block keeps when an operation adds factors beside the ones it
was written against.

`monomial_padE` says the widening changes no monomial — the new factors sit at
exponent zero — which is the only reason the block may be carried through
unchanged. It is what the definition is for, so it stays here.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

def ConPolyZono.padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ) :
    Fin (p + r) → Fin s → ℕ :=
  Fin.append EC fun _ _ => 0

theorem ConPolyZono.monomial_padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.padE EC r) a l
      = PolyZonotope.monomial EC (fun k => a (Fin.castAdd r k)) l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  -- the appended factors contribute a product of `1`s
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ ConPolyZono.padE EC r (Fin.natAdd p k) l) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [ConPolyZono.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ ConPolyZono.padE EC r (Fin.castAdd r k) l)
      = ∏ k, a (Fin.castAdd r k) ^ EC k l :=
    Finset.prod_congr rfl fun k _ => by
      simp only [ConPolyZono.padE, Fin.append_left]
  rw [hnew, hold, mul_one]

end CORALean.Real
