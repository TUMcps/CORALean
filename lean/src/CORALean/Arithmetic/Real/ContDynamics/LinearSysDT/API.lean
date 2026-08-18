import CORALean.Arithmetic.Real.ContSet.ContSet.API

/-!
# Discrete-time linear systems: representation and reachability

CORA's `linearSysDT`: `x(k+1) = A x(k) + u(k)`.

`reach` is written against `OuterContSet`, so it runs at any representation
offering the three operations. `Trajectory` is the only place the dynamics
appear.

`reduce` is called once per step, which is what holds the representation at
order `o`; nothing in the types enforces that, and nothing needs to.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix ContSet Scalar OuterContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S 𝕋]

structure LinearSysDT (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

/-- The reachable set after `k` steps, from initial set `R₀` under inputs `U`,
held at maximum order `o`. -/
def LinearSysDT.reach (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce o (plus (mtimes sys.A (sys.reach o R₀ U k)) U)

/-- One admissible run. Inputs are per step, so a disturbance is one too. -/
structure LinearSysDT.Trajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

end CORALean.Arithmetic.Real
