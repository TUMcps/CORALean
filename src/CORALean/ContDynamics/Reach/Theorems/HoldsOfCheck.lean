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

## Inputs
* `sys` – system
* `params` – reachability parameters
* `options` – reachability options
* `spec` – specification

## Hypotheses
* none

## Conclusion
* a passed check gives the specification on the exact reachable set
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSetLike

variable {Sys : ℕ → Type u} {Params : (n : ℕ) → Sys n → Type} {Options : Type}
variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)]
variable {n : ℕ} {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.holds_of_check [Reach Sys Params Options ContSet₂]
    [Contains ContSet₁ (SetUnion (ContSet₂ n))] [IsDisjoint ContSet₁ (SetUnion (ContSet₂ n))]
    (sys : Sys n) (params : Params n sys) (options : Options)
    (spec : Specification ContSet₁) : -- --- CONCL ---
    Reach.check (ContSet₂ := ContSet₂) sys params options spec →
    (spec.Holds (Reach.reachExact (ContSet := ContSet₂) sys params)) := by -- --- PROOF ---
  unfold Reach.check
  -- `none` checks `false`, so only a returned set is left, and it encloses
  cases hR : Reach.reach (ContSet := ContSet₂) sys params options with
  | none => intro h; exact absurd h Bool.false_ne_true
  | some R =>
    intro h
    exact spec.holds_of_outer (Reach.reach_outer sys params options hR) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
