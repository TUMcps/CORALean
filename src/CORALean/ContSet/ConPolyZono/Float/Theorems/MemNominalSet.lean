module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal constrained polynomial zonotope

The form every enclosure proof at this layer reads the nominal half of a point
in: the centre and the two generator blocks through `toReal`, the exponent
matrices unrounded, and the constraint as this set's own `satisfies`.

Proofs use it rather than going through `nominal` because through it every count
is `cPZ.h`, where the instance gives the equal-but-distinct `(nominal cPZ).h` that
`rw` reads apart.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet cPZ ↔ ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ cPZ.satisfies a ∧ ∀ i, x i = toReal (cPZ.c i)
        + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E a l)
        + ∑ j, toReal (cPZ.GI j i) * β j :=
  Real.ConPolyZono.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
