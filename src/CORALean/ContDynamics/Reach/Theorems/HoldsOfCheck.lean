import CORALean.ContDynamics.Reach.Reach
import CORALean.Specification.Theorems.CheckSound
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A passed check on `reach` holds on `reachExact`, for every system class

`check_sound` puts the specification on what `reach` denotes, and `reach_outer`
is the outer approximation `holds_of_outer` carries it back across: a `true`,
found by evaluation, is the specification on the exact reachable set, at any
instance of `Reach` and with nothing left to prove by hand. `reachExact` never
mentions `S`, so the class leaves it explicit there, named `(S := S)` below.
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
    (spec.check (Reach.reach sys p X₀) = true) →
    (spec.Holds (Reach.reachExact (S := S) sys p (construct X₀))) :=
  fun h => spec.holds_of_outer (Reach.reach_outer sys p X₀) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
