module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ConZonotope.keepEmbed`

The kept coefficients of a partition, put back into the full coefficient space with
zero in every dropped coordinate. Composing a constraint with it reads the
constraint at a point whose dropped coefficients are zero, which is the first half
of what `keepRows` does to each row.

## Inputs
* `part` – partition of the generators

## Output
* the map putting kept coefficients back into the full space
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {h q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept coordinates `part.left` of a coefficient vector in `Vec ℝ q`, zero in the
`part.right` ones: `∑ l, v l • e_{left l}`. -/
def ConZonotope.keepEmbed (part : Split (Fin h) into (Fin q) ⊕ (Fin r)) :
    Vec ℝ q →ₗ[ℝ] Vec ℝ h where
  toFun v := ∑ l, v l • (Pi.single (part.left l) (1 : ℝ) : Vec ℝ h)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
