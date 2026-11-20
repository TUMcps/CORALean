module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongest
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitFactorOuter

@[expose] public section

/-!
# `PolyZonotope.splitLongest` covers the set

Whichever factor the lengths select, its split covers the set (`splitFactor_outer`).

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongest_outer (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ P ∈ pZ.splitLongest, pZ.toSet ⊆ P.1.toSet ∪ P.2.toSet := by -- --- PROOF ---
  intro P h
  unfold PolyZonotope.splitLongest at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact PolyZonotope.splitFactor_outer pZ k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
