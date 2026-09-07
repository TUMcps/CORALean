import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A polynomial zonotope as a zonotope

CORA's `zonotope(polyZonotope)` in its cheapest form: read every dependent
generator as an independent one. Sound because a monomial in factors of `[-1,1]`
is itself in `[-1,1]`, so each dependent coefficient is a coefficient a zonotope
already admits.

What is lost is the *sharing*, which is the whole representation: the dependent
generators are freed to move independently, so the result is the convex zonotope
that the coupling was cutting down. Every non-convexity goes, and so does the
exactness of a quadratic map — nothing of the exponent matrix survives but the
generator vectors it indexed.

Not tight: CORA also offers a tighter enclosure that treats an even exponent
separately, since `α^2` ranges over `[0,1]` rather than `[-1,1]` and its
generator can be halved and its centre shifted. That is a second conversion, not
this one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.zonotope (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at the generator count this conversion produces, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_zonotope {pZ : PolyZonotope α} (f : Fin (pZ.h + pZ.q) → α) :
    ∑ l : Fin pZ.zonotope.h, f l
      = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotope_outer (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonotope.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (PolyZonotope.monomial pZ.E a) b, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.abs_monomial_le_one pZ.E ha i
    · intro j
      simpa using hb j
  · rw [PolyZonotope.aux_sum_univ_zonotope]
    simp only [PolyZonotope.zonotope, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
