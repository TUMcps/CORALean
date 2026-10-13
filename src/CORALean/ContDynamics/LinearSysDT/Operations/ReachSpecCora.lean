import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Order.Interval.Finset.Nat

/-!
# `LinearSysDT.reachSpecCora`

The verdict `res` of CORA's `@linearSysDT/reach.m` called with an unsafe-set specification, for
`ℝ¹`, `B = 0`, no disturbance, no noise, `C = 1`, `D = 0` (so `outputSet` returns its argument,
ll. 91, 152) and `linAlg = 'standard'`. `Rnext.tp` starts at `R0` (l. 82) and is mapped by
`x ↦ A x + c` in the step of l. 99. The loop `for i = 1:steps` (l. 85) stores the output set at
the beginning of step `i`, `Rout{i} = Rnext.tp` after `i - 1` steps (l. 91), and checks that one
against the specification (l. 129). After the loop `Rout{end} = Rout{steps+1}` is computed
(l. 152) and returned, never checked.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `res`: every checked output set is disjoint from the unsafe set. -/
def LinearSysDT.reachSpecCora (A c : ℝ) (R₀ F : Set ℝ) (steps : ℕ) : Prop :=
  let Rtp : ℕ → Set ℝ := fun k => (fun x => A * x + c)^[k] '' R₀    -- 82, 99. Rnext.tp
  let Rout : ℕ → Set ℝ := fun i => Rtp (i - 1)                      -- 91. Rout{i}
  ∀ i ∈ Finset.Icc 1 steps, Disjoint (Rout i) F                -- 85, 129. check(spec,Rout{i})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
