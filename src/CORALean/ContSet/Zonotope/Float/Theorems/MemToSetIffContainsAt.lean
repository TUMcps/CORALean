module

public import CORALean.ContSet.Zonotope.Float.Definitions.ContainsAt
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A point is in a float zonotope exactly at some weights of its generators

`Zonotope.toSet` is the nominal zonotope plus the error box, and a point of the nominal part is
the center plus the generators weighted by some `β` in the unit cube. Collecting the box point and
the weights, the point is in the set if and only if it is in it at some `β`.

## Inputs
* `Z` – zonotope
* `x` – point

## Hypotheses
* none

## Conclusion
* the point is in the zonotope if and only if it is there at some weights
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_toSet_iff_containsAt {Z : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n} : -- --- CONCL ---
    x ∈ Z.toSet ↔ ∃ β, Z.ContainsAt β x := by -- --- PROOF ---
  constructor
  · rintro ⟨a, ha, e, he, rfl⟩
    obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp ha
    exact ⟨β, hβ, e, he, fun i => by simp only [Pi.add_apply, hx i]⟩
  · rintro ⟨β, hβ, e, he, hx⟩
    exact ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩, e, he,
      funext fun i => (hx i).symm⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
