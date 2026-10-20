module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `pointLo` and `pointHi` bracket `c + G β`

Each end is a rounded evaluation of the same expression: `addDown_le_add` with `dotDown_le`, and
`add_le_addUp` with `le_dotUp`.

## Inputs
* `Z` – zonotope
* `β` – factor vector
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* exact point lies between the two rounded evaluations
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.point_between (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h)
    (i : Fin n) : -- --- CONCL ---
    toReal (Z.pointLo β i) ≤ toReal (Z.c i) + ∑ j, toReal (Z.G j i) * toReal (β j)
      ∧ toReal (Z.c i) + ∑ j, toReal (Z.G j i) * toReal (β j)
        ≤ toReal (Z.pointHi β i) := by -- --- PROOF ---
  have h1 := addDown_le_add (Z.c i) (dotDown (fun j => Z.G j i) β)
  have h2 := add_le_addUp (Z.c i) (dotUp (fun j => Z.G j i) β)
  have h3 := dotDown_le (fun j => Z.G j i) β
  have h4 := le_dotUp (fun j => Z.G j i) β
  exact ⟨by simp only [Zonotope.pointLo]; linarith, by simp only [Zonotope.pointHi]; linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
