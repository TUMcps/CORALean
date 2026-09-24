import CORALean.ContDynamics.Reach.Operations.Check
import CORALean.Specification.Theorems.CheckSound
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A passed check on `reach` holds on `reachExact`, for every system class

A `true` from `Reach.check` means `reach` returned a set and the specification
checked on it: `check_sound` puts the specification on what that set denotes,
and `reach_outer` is the outer approximation `holds_of_outer` carries it back
across. Found by evaluation, it is the specification on the exact reachable set,
at any instance of `Reach` and with nothing left to prove by hand. `reachExact`
never mentions `S`, so the class leaves it explicit there, named `(S := S)`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet

variable {Sys : ℕ → Type u} {Params : Type} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {n : ℕ} {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.holds_of_check [Reach Sys Params S] [Contains ContSet (SetUnion (S n))]
    [IsDisjoint ContSet (SetUnion (S n))] (sys : Sys n) (p : Params) (X₀ : S n)
    (spec : Specification ContSet) :
    (Reach.check sys p X₀ spec = true) →
    (spec.Holds (Reach.reachExact (S := S) sys p (construct X₀))) := by -- --- PROOF ---
  unfold Reach.check
  -- `none` checks `false`, so only a returned set is left, and it encloses
  cases hR : Reach.reach sys p X₀ with
  | none => intro h; exact absurd h Bool.false_ne_true
  | some R =>
    intro h
    have hout := Reach.reach_outer sys p X₀
    rw [hR] at hout
    exact spec.holds_of_outer hout (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
