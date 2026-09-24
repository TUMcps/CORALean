import CORALean.Specification.Specification

/-!
# Checking a specification on a computed set

CORA's `check`, for a computed set held in a representation: the specification's own
set is asked about it, `contains` for a safe set or an invariant, `isDisjoint` for an
unsafe one. Both are the representation pair's instances, as `mtimes` is `Mtimes`'s,
so `check` computes whenever they do; `Theorems.CheckSound` is what a `true` buys.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet S α : Type} [CORALean.ContSet ContSet α] [CORALean.ContSet S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `false` means only "not shown": both instances may be conservative. -/
def Specification.check [Contains ContSet S] [IsDisjoint ContSet S]
    (spec : Specification ContSet) (s : S) : Bool :=
  match spec.kind with
  | .safeSet => Contains.contains spec.set s
  | .unsafeSet => IsDisjoint.isDisjoint spec.set s
  | .invariant => Contains.contains spec.set s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
