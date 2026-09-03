import CORALean.ContSet.ContSet.ContSet

/-!
# Discrete-time linear systems: the representation

CORA's `linearSysDT`, reduced to `x(k+1) = A x(k) + u(k)`: the class there is
`x(k+1) = A x(k) + B u(k) + c` with an output `y = C x + D u + k`, and here only
`A` is kept, the input entering in state coordinates as in Althoff's thesis.
`B U ⊕ c` is one `mtimes` and one `plus` on the input set, and every state the
system can reach is reached in the folded form too, so the state dynamics lose
nothing by it.

The output equation is `OutputEq`, paired with a reachable set rather than
stored here — `LinearSysDT.output_outer` is the pairing along a run. Its `D`
multiplies the input in *state* coordinates, which is where folding `B` does
cost something: CORA's `D u` is recovered from it only when `B` is invertible,
so feedthrough of an input `B` annihilates cannot be written. That is the one
argument for an explicit `B`, and it arrives with the output equation and not
before it.

`Trajectory` is what such a system denotes and the only place the dynamics
appear — one admissible run, with an input per step, so a disturbance is one
too.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure LinearSysDT (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSysDT.Trajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

end CORALean.Real
