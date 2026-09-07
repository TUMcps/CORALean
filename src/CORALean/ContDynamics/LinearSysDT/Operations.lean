import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# Discrete-time linear systems: reachability

`reach` is written against `Plus` and `Reduce` and names no other operation, so
it runs at a representation that has no `linComb` — which is the point of an
operation being a class of its own.

`reduce` is called once per step, which is what holds the representation at
order `o`. `reach` demands `0 < o`: at `o = 0`, `Zonotope.reduceGirard`'s
natural subtraction keeps `(0 - 1) * n = 0` generators, silently returning
order 1 — stricter than CORA, whose `pickedGeneratorsFast` goes negative below
order 1 and whose `@zonotope/reduce` checks `order` not at all.

`reachHeld` is `reach` restricted to `𝕋 = ℝ` and a single held input, in closed
form, needing no `reduce` and so no `0 < o`.

`simulate` samples one run rather than enclosing all of them: a point
computation, so it carries none of `reach`'s set instances.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

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

variable [Mtimes (Mat ℝ) S]

/-- `reach` at one held point of `U`: `U` multiplied once by `∑ i < N, Aⁱ`, not
accumulated per step, so a zero-order hold reads off exactly rather than through
the jitter a fresh point of `U` at every step would add. -/
def LinearSysDT.reachHeld (sys : LinearSysDT ℝ n) (R₀ U : S n) (N : ℕ) : S n :=
  plus (mtimes (sys.A ^ N) R₀) (mtimes (∑ i ∈ Finset.range N, sys.A ^ i) U)

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
    [Mtimes (Mat 𝕋) S] [Mtimes (Mat ℝ) S] in
/-- One sampled run of the dynamics from `x₀` under input signal `u` — a point
computation, none of `reach`'s set instances needed. -/
def LinearSysDT.simulate (sys : LinearSysDT 𝕋 n) (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ n) :
    ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => toRealMat sys.A *ᵥ sys.simulate x₀ u k + u k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
