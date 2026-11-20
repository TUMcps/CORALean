module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitFactor
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FoldConstantsOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PickOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitDepFactorOuter

@[expose] public section

/-!
# `PolyZonotope.splitFactor` covers the set

The two substitutions cover the set (`splitDepFactor_outer`); picking the columns, folding the
constants (`foldConstants_outer`) each only enlarge a half. Outer, not exact.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor to split

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

theorem PolyZonotope.splitFactor_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (k : Fin pZ.p) : -- --- CONCL ---
    pZ.toSet ⊆ (pZ.splitFactor k).1.toSet ∪ (pZ.splitFactor k).2.toSet := by -- --- PROOF ---
  -- each half of the cover lies in the matching half here
  have grow : ∀ (S : PolyZonotope (Vec 𝕋 n)) (m : ℕ) (idx : Fin m → ℕ),
      S.toSet ⊆ (S.pick m idx).foldConstants.toSet := fun S m idx =>
    subset_trans (PolyZonotope.pick_outer S m idx) (PolyZonotope.foldConstants_outer _)
  intro x hx
  rcases PolyZonotope.splitDepFactor_outer pZ k hx with h | h
  · exact Or.inr (grow _ _ _ h)
  · exact Or.inl (grow _ _ _ h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
