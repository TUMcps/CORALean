module

public import CORALean.ContDynamics.Interfaces
public import CORALean.Specification.Operations.Check

@[expose] public section

/-!
# Checking a specification on what `reach` returns

`reach(sys, params, options)` and then `check`, as a CORA script runs them, at any
instance of `Reach`: if `reach` returned a set, `Specification.check` it. A `reach` that
returned `none` could not certify its own soundness conditions, so it verifies
nothing and the answer is `false`, the "not shown" a conservative `Contains`
gives.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

variable {Sys : ℕ → Type u} {P : ℕ → Type} {O : Type} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {n : ℕ} {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spec` checked on `reach sys params options`; `false` if `reach` returned `none`. -/
def Reach.check [Reach Sys P O S] [Contains ContSet (SetUnion (S n))]
    [IsDisjoint ContSet (SetUnion (S n))] (sys : Sys n) (params : P n) (options : O)
    (spec : Specification ContSet) : Bool :=
  match Reach.reach (S := S) sys params options with
  | some R => spec.check R
  | none => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
