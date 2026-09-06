import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct

/-!
# Membership in the nominal polynomial zonotope, in the stored fields

The form every enclosure proof at this layer reads the nominal half of a point
in. The exponent matrix is over ℕ and is not rounded, so the monomials here are
the exact layer's monomials rather than roundings of them; only the two
generator blocks and the centre pass through `toReal`.

Proofs use it rather than going through `nominal` because through it every count
is `PZ.h`, where the instance gives the equal-but-distinct `(nominal PZ).h` that
`rw` reads apart.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {PZ : PolyZonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet PZ ↔ ∃ a : Fin PZ.p → ℝ, ∃ β : Fin PZ.q → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = toReal (PZ.c i)
        + (∑ l, toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
        + ∑ j, toReal (PZ.GI i j) * β j :=
  Real.PolyZonotope.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
