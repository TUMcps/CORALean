module

public import CORALean.ContSet.ConZonotope.Float.Operations.ZeroFeasible
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.ContainsOriginSound

@[expose] public section

/-!
# A constrained zonotope that passes `zeroFeasible` is nonempty

Coefficients `0` meet the unit box, and meet every row by the constraint's own
`HPolytope.containsOrigin_sound`; the point they name is the center.

## Inputs
* `cZ` – float constrained zonotope

## Hypotheses
* `h` – the test answers true

## Conclusion
* the nominal set is nonempty
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zeroFeasible_nonempty {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (h : cZ.zeroFeasible = true) :
    (nominalSet cZ).Nonempty := by
  exact ⟨fun i => toReal (cZ.c i), ConZonotope.mem_nominalSet_iff.mpr
    ⟨0, fun j => by simp, HPolytope.containsOrigin_sound h, fun i => by simp⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
