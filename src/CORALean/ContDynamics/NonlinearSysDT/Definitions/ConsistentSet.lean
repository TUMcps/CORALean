import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
import Mathlib.Data.Real.Basic

/-!
# The states consistent with a measured output, nonlinear

[1, Def. 4]: for the measurement map `g(x, v)` with noise `v ∈ V`, the consistent state set of a
measured output `y` is `X_y = {x | y ∈ g(x, V)}`. `consistentSetComp` is the part of it that one
component `y i` of the output determines, `X_y(i) = {x | y i ∈ g_i(x, V)}` of [1, Sec. 5], from
which the strips of [1, Property 1] are taken. `g` is an argument: `NonlinearSysDT` carries the
update map `f` only. No representation: `V` is any set, and so are the results.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X_y = {x | y ∈ g(x, V)}`. -/
def NonlinearSysDT.consistentSet {n nv p : ℕ} (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p)
    (V : Set (Vec ℝ nv)) (y : Vec ℝ p) : Set (Vec ℝ n) :=
  {x | ∃ v ∈ V, y = g x v}

/-- `X_y(i) = {x | y i ∈ g_i(x, V)}`. -/
def NonlinearSysDT.consistentSetComp {n nv p : ℕ} (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p)
    (V : Set (Vec ℝ nv)) (y : Vec ℝ p) (i : Fin p) : Set (Vec ℝ n) :=
  {x | ∃ v ∈ V, y i = g x v i}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
