import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# Discrete-time linear systems: reachability

`reach` is written against `Plus` and `Reduce` alone, so it runs at a
representation with no `linComb`.

`reduce` is called once per step, holding the representation at order `o`.
`reach` demands `0 < o`: at `o = 0`, `Zonotope.reduceGirard`'s natural
subtraction keeps `(0 - 1) * n = 0` generators, silently returning order 1 —
stricter than CORA, whose `pickedGeneratorsFast` goes negative below order 1.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   08-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `k` steps, from initial set `R₀` under inputs `U`,
held at maximum order `o`. `ho` is what rules out `o = 0`. -/
def LinearSysDT.reach (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o) (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce (plus (mtimes sys.A (sys.reach o ho R₀ U k)) U) o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
