module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Operations.Replace

@[expose] public section

/-!
# `ZonoBundle.replace` denotes `Z` and every other member, over a floating-point scalar

Exact: the family is only rearranged, so the denotation is `Z`'s inflated set intersected with
the inflated sets of the members other than `index`.

## Inputs
* `zB` – float zonotope bundle
* `index` – member to overwrite
* `Z` – replacement zonotope

## Hypotheses
* none

## Conclusion
* the result is the replacement intersected with the other members
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.replace_construct (zB : ZonoBundle (Vec 𝕋 n)) (index : Fin zB.k)
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (zB.replace index Z).construct =
      Z.construct ∩ ⋂ i : {i : Fin zB.k // i ≠ index}, (zB.Z i).construct := by -- --- PROOF ---
  ext x
  simp only [ZonoBundle.construct_eq_iInter, ZonoBundle.replace, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    refine ⟨by simpa using h index, fun i => ?_⟩
    simpa [Function.update_of_ne i.2] using h i.1
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = index
    · subst hi; simpa using h1
    · simpa [Function.update_of_ne hi] using h2 ⟨i, hi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
