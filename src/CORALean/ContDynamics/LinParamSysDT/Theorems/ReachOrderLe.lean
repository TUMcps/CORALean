import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContDynamics.LinParamSysDT.Operations.Simulate
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

/-!
# `LinParamSysDT.reach` bounds the generator count

`LinearSysDT.reach_order_le`'s statement and proof, character for character:
`reach` is the same recursion at a set-valued `sys.A`, so the last step still
ends in a `reduce`, and `reduce_order_le` closes it the same way, without
touching `k`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [Mtimes 𝕄 𝒵]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n`
generators, at every `S := 𝒵`: unfold one step of `reach` and `reduce_order_le`
bounds what it ends in. -/
theorem LinParamSysDT.reach_order_le (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) o ho R₀ U (k + 1)).h ≤ o * n :=
  Zonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
