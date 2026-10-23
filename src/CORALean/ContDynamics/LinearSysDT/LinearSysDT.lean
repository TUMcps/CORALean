module

public import CORALean.ContDynamics.OutputEq.Operations.Eval
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time linear systems: the representation

CORA's `linearSysDT`, `x(k+1) = A x(k) + B u(k) + c + E w(k)` with the output
`y(k) = C x(k) + D u(k) + k + F v(k)`, every matrix stored, `m` inputs, `q` outputs, `r`
disturbances, `s` noises, and CORA's sampling time `dt`. Runs and reachable sets are indexed by the
step `k`, the time `k dt`. `IsTrajectory` is a run of the whole equation; `IsCanonicalTrajectory` of
the canonical form, `x(k+1) = A x(k) + u'(k)` with `u' = B u + c + E w` in state coordinates, as
[1, Sec. I] absorbs `B u` into the input set in continuous time, what the reachability algorithms
are proved against; `IsTrajectory.canonical` turns every run into one. `IsCanonicalTrajectoryOn K`
is the canonical run known only for `k < K`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A discrete-time linear system `x⁺ = A x + B u + c + E w` with output `y = C x + D u + k + F v`,
as CORA's `linearSysDT`: all matrices stored, the dimensions `m q r s` and the sampling time `dt` as
fields. -/
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

/-- The output equation `y = C x + D u + k`, read off the system as stored; the noise term `F v`
stays with the system. -/
def LinearSysDT.outputEq (sys : LinearSysDT 𝕋 n) : OutputEq 𝕋 n sys.m sys.q :=
  ⟨sys.C, sys.D, sys.k⟩

/-- A run of the whole equation: the state from `X₀` under inputs in `U` and disturbances in
`W`, and the output under noise in `V`. -/
structure LinearSysDT.IsTrajectory (sys : LinearSysDT 𝕋 n) (X₀ : S n) (U : S sys.m)
    (W : S sys.r) (V : S sys.s) (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ sys.m)
    (w : ℕ → Vec ℝ sys.r) (v : ℕ → Vec ℝ sys.s) (y : ℕ → Vec ℝ sys.q) : Prop where
  init : x 0 ∈ construct X₀
  input (k : ℕ) : u k ∈ construct U
  dist (k : ℕ) : w k ∈ construct W
  noise (k : ℕ) : v k ∈ construct V
  step (k : ℕ) : x (k + 1) =
    toRealMat sys.A *ᵥ x k + toRealMat sys.B *ᵥ u k + toRealVec sys.c + toRealMat sys.E *ᵥ w k
  output (k : ℕ) : y k = sys.outputEq.eval (x k) (u k) + toRealMat sys.F *ᵥ v k

/-- A run of the canonical form, its combined input in state coordinates drawn from `U`. -/
structure LinearSysDT.IsCanonicalTrajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSys.IsCanonicalTrajectory`'s `x` and `u` are unconstrained
outside `T`. -/
structure LinearSysDT.IsCanonicalTrajectoryOn (sys : LinearSysDT 𝕋 n) (R₀ U : S n) (K : ℕ)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

/-- A zero-order hold: one point `u` of `U`, reused at every step, unlike
`IsCanonicalTrajectory` where `input` lets a fresh point be picked each time. -/
structure LinearSysDT.IsCanonicalHeldTrajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x : ℕ → Vec ℝ n) (u : Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input : u ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
