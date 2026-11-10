module

public import CORALean.Specification.Specification

@[expose] public section

/-!
# Checking a specification on a computed set

CORA's `check`, for a computed set held in a representation: the specification's own
set is asked about it, `contains` for a safe set or an invariant, `isDisjoint` for an
unsafe one. Both are the representation pair's instances, as `mtimes` is `Mtimes`'s,
so `check` computes whenever they do; `Theorems.CheckSound` is what a `true` buys.

## Inputs
* `spec` – specification
* `S` – computed set

## Output
* whether the set provably satisfies the specification
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet₁ ContSet₂ α : Type} [ContSetLike ContSet₁ α] [ContSetLike ContSet₂ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `false` means only "not shown": both instances may be conservative. -/
def Specification.check [Contains ContSet₁ ContSet₂] [IsDisjoint ContSet₁ ContSet₂]
    (spec : Specification ContSet₁) (S : ContSet₂) : Bool :=
  match spec.kind with
  | .safeSet => Contains.contains spec.set S
  | .unsafeSet => IsDisjoint.isDisjoint spec.set S
  | .invariant => Contains.contains spec.set S

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
