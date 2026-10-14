module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time linear systems with a set-valued system matrix

`x(k+1) = A(k) x(k) + u(k)` with `A(k)` ranging over a set `sys.A` at every step, not fixed
for the run — the system-matrix uncertainty of [1, Sec. 3.3]. CORA has no class of this name:
this is the discrete step inside CORA's `linParamSys/post`, `R(k+1) = M R(k) ⊕ R_input` with
`M` the enclosure `mappingMatrixSet` of `e^{AΔt}` over the parameter set, the loop of
[1, Alg. 4]. `LinParamSys.discretizeEnclosure` (and its float twin) produce one from a
`LinParamSys`, `LinearSys.discretizeMatZonotopeFloat` from a `LinearSys` whose `e^{AΔt}` is
only enclosed, and `LinearSysDT.toLinParam` embeds the point-matrix case, `𝕄 := Mat 𝕋`.
Like CORA's step it has no `B`, `c`, output or `dt`: the input is already in state
coordinates and steps are counted. `LinearSysDT` stays separate rather than being
re-expressed through this, a decision left open on #29.

`Trajectory.step` picks a fresh `A ∈ construct sys.A` at every `k`, mirroring
`LinearSysDT.reachHeld`'s distinction between a fresh input each step and one
held for the whole run: fixing one `A` for the run is a smaller, unexploited
set. `TrajectoryOn K` is the same, known only for `k < K`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinParamSysDT (𝕄 : ℕ → ℕ → Type) (n : ℕ) where
  A : 𝕄 n n

structure LinParamSysDT.Trajectory (sys : LinParamSysDT 𝕄 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : ∃ A ∈ construct sys.A, x (k + 1) = A *ᵥ x k + u k

/-- A run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSysDT.CanonicalTrajectoryOn`'s are. -/
structure LinParamSysDT.TrajectoryOn (sys : LinParamSysDT 𝕄 n) (R₀ U : S n) (K : ℕ)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : ∃ A ∈ construct sys.A, x (k + 1) = A *ᵥ x k + u k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
