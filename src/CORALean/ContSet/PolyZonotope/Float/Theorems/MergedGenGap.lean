import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp

/-!
# What storing the merged column costs

Every exponent relaxation merges the same two dependent columns and stores their
sum at its lower rounding, so every one of them owes the same gap: the distance
up to the sum taken at the *upper* rounding, which `generatorError` charges at
the surviving column's monomial.

Stated against that gap written out rather than against a row of one operation's
gap matrix, so that `relaxExp`, `relaxExpEven` and `relaxExpMid` each read it at
their own matrix without the fact being proved three times. The row reduces to
this expression, which is why each reads it by `exact`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The merged column is stored downward, so it is off by at most its gap to the
upward rounding. -/
theorem PolyZonotope.mergedGen_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (i : Fin n) :
    |toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
      - toReal (PZ.mergedGen part i)|
      ≤ toReal (subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0)))
        (PZ.mergedGen part i)) := by
  have hlo : toReal (PZ.mergedGen part i)
      ≤ toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0)) := addDown_le_add _ _
  have hhi : toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
      ≤ toReal (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) := add_le_addUp _ _
  have hgap : toReal (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0)))
      - toReal (PZ.mergedGen part i)
      ≤ toReal (subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0)))
        (PZ.mergedGen part i)) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
