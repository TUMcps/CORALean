module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time linear systems: the representation

CORA's `linearSysDT`, reduced to `x(k+1) = A x(k) + u(k)`: the class there is
`x(k+1) = A x(k) + B u(k) + c` with an output `y = C x + D u + k`, and here only
`A` is kept, the input entering in state coordinates as in [1, Sec. 3.2]. `B U ⊕ c` is one
`mtimes` and one `plus` on the input set, and the folded form reaches every state
the system can.

The output equation is `OutputEq`, paired with a reachable set rather than
stored here — `output_outer` pairs it along a run. `D` multiplies the input in
*state* coordinates, unrecoverable once `B` folds away.

`Trajectory` is the only place the dynamics appear — one run, quantified over
every `k : ℕ`. `TrajectoryOn K` is the same, known only for `k < K` — what
sampling on `[0, KΔt]` gives, never a total run, so `discretize_horizon`
produces it and `reach_outer_horizon` consumes it. No `bound` field on
`Trajectory` — every total run would then carry a spurious `K = ⊤` —
`toTrajectoryOn` gives `TrajectoryOn K` at any `K` from one instead.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSysDT.Trajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSys.Trajectory`'s `x` and `u` are unconstrained
outside `T`. -/
structure LinearSysDT.TrajectoryOn (sys : LinearSysDT 𝕋 n) (R₀ U : S n) (K : ℕ)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A zero-order hold: one point `u` of `U`, reused at every step, unlike
`Trajectory` where `input` lets a fresh point be picked each time. -/
structure LinearSysDT.HeldTrajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x : ℕ → Vec ℝ n) (u : Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input : u ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
