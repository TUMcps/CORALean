module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal polynomial zonotope, in the stored fields

The form every enclosure proof at this layer reads the nominal half of a point
in. The exponent matrix is over ℕ and is not rounded, so the monomials here are
the exact layer's monomials rather than roundings of them; only the two
generator blocks and the center pass through `toReal`.

Proofs use it rather than going through `nominal` because through it every count
is `pZ.h`, where the instance gives the equal-but-distinct `(nominal pZ).h` that
`rw` reads apart.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {pZ : PolyZonotope (Vec 𝕋 n)}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet pZ ↔ ∃ a : Fin pZ.p → ℝ, ∃ β : Fin pZ.q → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = toReal (pZ.c i)
        + (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
        + ∑ j, toReal (pZ.GI j i) * β j :=
  Real.PolyZonotope.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
