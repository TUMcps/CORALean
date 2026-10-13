import CORALean.Global.DmdBlocks

/-!
# `[A c B]` from its blocks

The matrix `dmdBlocks` takes apart: `A` in the first `n` columns, `c` in column `n + 1`, `B`
in the last `m`.
The source is [1].

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[A c B]`. -/
def dmdStack (A : Mat ℝ n n) (B : Mat ℝ n m) (c : Vec ℝ n) : Mat ℝ n (n + 1 + m) :=
  fun i => Fin.append (Fin.snoc (α := fun _ => ℝ) (A i) (c i)) (B i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
