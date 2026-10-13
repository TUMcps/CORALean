import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct

/-!
# Membership in the nominal constrained zonotope, in the stored fields

The form every enclosure proof at this layer reads the nominal half of a point
in: the centre and the generators through `toReal`, and the constraint as
membership in the float polytope's own `construct`, which has already absorbed
its rounding into an interval right-hand side.

Proofs use it rather than going through `nominal` because through it every count
is `cZ.h`, where the instance gives the equal-but-distinct `(nominal cZ).h`.
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

theorem ConZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet cZ ↔ ∃ β : Vec ℝ cZ.h, (∀ j, |β j| ≤ 1)
      ∧ β ∈ cZ.P.construct
      ∧ ∀ i, x i = toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * β j :=
  Real.ConZonotope.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
