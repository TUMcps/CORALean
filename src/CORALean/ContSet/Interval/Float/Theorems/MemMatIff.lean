import CORALean.ContSet.Interval.Float.Interval

/-!
# Membership in a float interval matrix, entry by entry

`Real.Interval.mem_mat_iff` read through `nominal`: both bounds are the stored
floats read as reals, so the statement needs no unfolding at the use site.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_mat_iff {I : Interval (Mat 𝕋 m n)} {A : Mat ℝ m n} :
    A ∈ I.construct ↔ ∀ i j, toReal (I.inf i j) ≤ A i j ∧ A i j ≤ toReal (I.sup i j) :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
