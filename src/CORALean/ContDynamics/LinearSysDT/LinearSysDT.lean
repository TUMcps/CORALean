module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time linear systems: the representation

CORA's `linearSysDT`, `x(k+1) = A x(k) + B u(k) + c + E w(k)` with the output
`y(k) = C x(k) + D u(k) + k + F v(k)`, every matrix stored, the dimensions beside `n` fields as
in `LinearSys`: `m` inputs, `q` outputs, `r` disturbances, `s` noises, and CORA's sampling
time `dt`. Runs and reachable sets are indexed by the step `k`, the time `k dt`, as CORA's
`reach` and `simulate` step through `tStart:dt:tFinal`; `dt` is what a conversion to
continuous time reads (`toLinearSys`) and what a discretization stores (`LinearSys.discretize`).

`Trajectory` is a run of the whole equation. `CanonicalTrajectory` is a run of the canonical
form, `x(k+1) = A x(k) + u'(k)` with the combined input `u' = B u + c + E w` in state
coordinates, as in [1, Sec. 3.2]: what the reachability algorithms, which read `A` and an input
set in state coordinates, are proved against. `Trajectory.canonical` turns every run into one.
`CanonicalTrajectoryOn K` is the canonical run known only for `k < K` — what sampling on
`[0, KΔt]` gives, so `discretize_horizon` produces it and `reach_outer_horizon` consumes it;
`toTrajectoryOn` gives it at any `K` from a total run. `CanonicalHeldTrajectory` holds one
input for the whole run.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT (𝕋 : Type) (n : ℕ) where
  m : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
  A : Mat 𝕋 n n
  B : Mat 𝕋 n m
  c : Vec 𝕋 n
  C : Mat 𝕋 q n
  D : Mat 𝕋 q m
  k : Vec 𝕋 q
  E : Mat 𝕋 n r
  F : Mat 𝕋 q s
  dt : 𝕋

/-- A run of the whole equation: the state from `X₀` under inputs in `U` and disturbances in
`W`, and the output under noise in `V`. -/
structure LinearSysDT.Trajectory (sys : LinearSysDT 𝕋 n) (X₀ : S n) (U : S sys.m)
    (W : S sys.r) (V : S sys.s) (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ sys.m)
    (w : ℕ → Vec ℝ sys.r) (v : ℕ → Vec ℝ sys.s) (y : ℕ → Vec ℝ sys.q) : Prop where
  init : x 0 ∈ construct X₀
  input (k : ℕ) : u k ∈ construct U
  dist (k : ℕ) : w k ∈ construct W
  noise (k : ℕ) : v k ∈ construct V
  step (k : ℕ) : x (k + 1) =
    toRealMat sys.A *ᵥ x k + toRealMat sys.B *ᵥ u k + toRealVec sys.c + toRealMat sys.E *ᵥ w k
  output (k : ℕ) :
    y k = toRealMat sys.C *ᵥ x k + toRealMat sys.D *ᵥ u k + toRealVec sys.k + toRealMat sys.F *ᵥ v k

/-- A run of the canonical form, its combined input in state coordinates drawn from `U`. -/
structure LinearSysDT.CanonicalTrajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSys.CanonicalTrajectory`'s `x` and `u` are unconstrained
outside `T`. -/
structure LinearSysDT.CanonicalTrajectoryOn (sys : LinearSysDT 𝕋 n) (R₀ U : S n) (K : ℕ)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A zero-order hold: one point `u` of `U`, reused at every step, unlike
`CanonicalTrajectory` where `input` lets a fresh point be picked each time. -/
structure LinearSysDT.CanonicalHeldTrajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x : ℕ → Vec ℝ n) (u : Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input : u ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
