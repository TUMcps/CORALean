module

public import CORALean.ContDynamics.Reach.Operations.Check
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A passed check on `reach` holds on `reachExact`, for every system class

A `true` from `Reach.check` means `reach` returned a set and the specification
checked on it: `check_sound` puts the specification on what that set denotes,
and `reach_outer` is the outer approximation `holds_of_outer` carries it back
across. Found by evaluation, it is the specification on the exact reachable set,
at any instance of `Reach` and with nothing left to prove by hand. No argument
fixes `S` for instance search, `P` being an output of it, so `S` is named, `(S := S)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet

variable {Sys : ℕ → Type u} {P : ℕ → Type} {O : Type} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {n : ℕ} {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.holds_of_check [Reach Sys P O S] [Contains ContSet (SetUnion (S n))]
    [IsDisjoint ContSet (SetUnion (S n))] (sys : Sys n) (params : P n) (options : O)
    (spec : Specification ContSet) :
    Reach.check (S := S) sys params options spec →
    (spec.Holds (Reach.reachExact (S := S) sys params)) := by -- --- PROOF ---
  unfold Reach.check
  -- `none` checks `false`, so only a returned set is left, and it encloses
  cases hR : Reach.reach (S := S) sys params options with
  | none => intro h; exact absurd h Bool.false_ne_true
  | some R =>
    intro h
    exact spec.holds_of_outer (Reach.reach_outer sys params options hR) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
