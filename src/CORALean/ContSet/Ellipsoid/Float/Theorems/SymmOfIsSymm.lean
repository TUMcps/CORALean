module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A symmetry check, read as reals

`isSymm` compares each pair of mirrored entries with `le` both ways; `le` is sound, so each
comparison holds as reals, and the two inequalities make the entries equal.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed `isSymm` makes the stored matrix, read as reals, symmetric. -/
theorem Ellipsoid.symm_of_isSymm [SoundFloatArithmetic 𝕋] {Q : Mat 𝕋 n n}
    (h : Ellipsoid.isSymm Q = true) (i j : Fin n) : toReal (Q i j) = toReal (Q j i) :=
  have hle : ∀ i j, toReal (Q i j) ≤ toReal (Q j i) := fun i j => toReal_le_of_le
    (List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j))
  le_antisymm (hle i j) (hle j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
