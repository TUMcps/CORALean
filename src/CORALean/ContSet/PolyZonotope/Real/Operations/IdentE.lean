import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.identE`

The identity exponent matrix: factor `i` appears in generator `i` alone and to
the first power, so its monomial is the factor itself — what a free coefficient
looks like once it has been made dependent.

This is the block `dependent` appends, and what a zonotope's generators become
when they are converted into dependent ones. The monomial it produces is the
whole point of it, so that lemma stays here.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

def PolyZonotope.identE (m : ℕ) : Fin m → Fin m → ℕ := fun k i => if k = i then 1 else 0

theorem PolyZonotope.monomial_identE {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    PolyZonotope.monomial (PolyZonotope.identE m) a i = a i := by
  rw [PolyZonotope.monomial, Finset.prod_eq_single i]
  · have h1 : PolyZonotope.identE m i i = 1 := if_pos rfl
    rw [h1, pow_one]
  -- every other factor sits at exponent zero
  · intro k _ hk
    have h0 : PolyZonotope.identE m k i = 0 := if_neg hk
    rw [h0, pow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real
