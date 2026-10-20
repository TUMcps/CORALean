module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal constrained zonotope, in the stored fields

The form every enclosure proof at this layer reads the nominal half of a point
in: the center and the generators through `toReal`, and the constraint as
membership in the float polytope's nominal part: the coefficient polytope's own error box is
not read, its rounding having been paid into its rows.

Proofs use it rather than going through `nominal` because through it every count
is `cZ.h`, where the instance gives the equal-but-distinct `(nominal cZ).h`.

## Inputs
* `cZ` – float constrained zonotope
* `x` – point

## Hypotheses
* none

## Conclusion
* membership in the nominal set means a unit-box coefficient vector meeting the constraints
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       04-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet cZ ↔ ∃ β : Vec ℝ cZ.h, (∀ j, |β j| ≤ 1)
      ∧ β ∈ cZ.P.nominal.construct
      ∧ ∀ i, x i = toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * β j :=
  Real.ConZonotope.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
