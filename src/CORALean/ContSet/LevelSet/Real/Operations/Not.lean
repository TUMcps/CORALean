import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# `LevelSet.not`

CORA's `@levelSet/not`: the complement of a single-constraint level set with operator `<=` or `<`,
which is `-f < 0` or `-f <= 0`. Every other level set (several constraints, or `==`) makes CORA
throw `notSupported`, which is `none` here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet/not`: negate the one function and swap `≤` with `<`. -/
def LevelSet.not (L : LevelSet n) : Option (LevelSet n) :=
  match L with
  | ⟨1, f, op⟩ =>
    match op 0 with
    | .le => some ⟨1, fun x i => -f x i, fun _ => .lt⟩
    | .lt => some ⟨1, fun x i => -f x i, fun _ => .le⟩
    | .eq => none
  | _ => none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
