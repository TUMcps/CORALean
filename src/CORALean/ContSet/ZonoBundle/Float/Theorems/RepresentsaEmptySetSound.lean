module

public import CORALean.ContSet.ZonoBundle.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ConZonotope.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
public import CORALean.ContSet.Conversion.Float.Theorems.ZonoBundleConZonotopeAllContains

@[expose] public section

/-!
# A `true` from `ZonoBundle.representsa_emptySet` proves the intersection empty

The bundle's points are the enclosed program's (`ZonoBundle.conZonotopeAll_contains`), which a
`true` proves empty.

## Inputs
* `zB` – float zonotope bundle

## Hypotheses
* `h` – the test answers true

## Conclusion
* the bundle is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.representsa_emptySet_sound {zB : ZonoBundle (Vec 𝕋 n)}
    (h : zB.representsa_emptySet = true) : -- --- CONCL ---
    zB.construct = ∅ := by -- --- PROOF ---
  unfold ZonoBundle.representsa_emptySet at h
  split at h
  · rename_i hk
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have := ConZonotope.representsa_emptySet_sound h
    have hmem := zB.conZonotopeAll_contains hk hx
    rw [this] at hmem
    exact hmem
  · exact absurd h (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
