module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

@[expose] public section

/-!
# What the generators `reduceBy` absorbs contribute, so what the block must cover

## Inputs
* `Z` – zonotope
* `part` – split into kept and absorbed generators
* `β` – factor vector
* `i` – coordinate

## Hypotheses
* `hβ` – factors in the unit box

## Conclusion
* absorbed contribution is bounded by the row radius
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the absorbed generators contribute, so what the block must cover. -/
theorem Zonotope.abs_absorbed_le_radius (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |∑ l, toReal (Z.G (part.right l) i) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G (part.right l) i) i) := by -- --- PROOF ---
  exact abs_sum_le_radius (d := fun i l => Z.G (part.right l) i)
    (fun _ _ => le_refl _) (fun l => hβ (part.right l)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
