import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# Discrete-time linear systems: reachability

`reach` is written against `OuterContSet`, so it runs at any representation
offering the three operations.

`reduce` is called once per step, which is what holds the representation at
order `o`; nothing in the types enforces that, and nothing needs to.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar OuterContSet Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

/-- The reachable set after `k` steps, from initial set `R₀` under inputs `U`,
held at maximum order `o`. -/
def LinearSysDT.reach (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce (plus (mtimes sys.A (sys.reach o R₀ U k)) U) o

end CORALean.Real
