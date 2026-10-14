module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope, over a
floating-point scalar

The constraints are dropped, which can only enlarge the set; every other field is
carried across, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.polyZonotope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.polyZonotope.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨a, β, ha, hβ, _, hx⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  exact PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
