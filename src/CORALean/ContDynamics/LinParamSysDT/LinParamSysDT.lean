module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time linear systems with a set-valued system matrix

`x(k+1) = A(k) x(k) + B(k) u(k) + c` with `A(k)`, `B(k)` ranging over the sets `sys.A`, `sys.B`
at every step, not fixed for the run — the system-matrix uncertainty of [1, Sec. 3.3]. The
parameters are those of the continuous twin `LinParamSys` (`A`, `B` matrix sets, `c`, `m`); no
`dt`, steps being counted. CORA has no class of this name: this is the discrete step inside
`linParamSys/post`, `R(k+1) = M R(k) ⊕ R_input`, `M` the enclosure `mappingMatrixSet` of
`e^{AΔt}` and `R_input` the input solution of `V = B*U + c`, the loop of [1, Alg. 4].
`LinParamSys.discretizeEnclosure` (and its float twin) produce one, `LinearSys.discretize…` from
a `LinearSys`, and `LinearSysDT.toLinParam` embeds the point case `𝕄 := Mat 𝕋`. The reach takes
the input in state coordinates, `U' ⊇ B U ⊕ c` (`inputSet`), so it reads neither `B` nor `c`:
`IsCanonicalTrajectory` is the run of that form, `IsTrajectory.canonical` takes every run into it.
`LinearSysDT` stays separate, a decision left open on #29. `IsTrajectory` picks a fresh `A k`,
`B k` at every `k`, as `LinearSysDT.reachHeld` a fresh input; `IsCanonicalTrajectoryOn K` is the
canonical run known for `k < K`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinParamSysDT (𝕄 : ℕ → ℕ → Type) (n : ℕ) where
  A : 𝕄 n n
  m : ℕ
  B : 𝕄 n m
  c : Vec ℝ n

/-- A run of the whole equation: a fresh `A k ∈ construct sys.A` and `B k ∈ construct sys.B` at
every step, under inputs in `U`. -/
structure LinParamSysDT.IsTrajectory (sys : LinParamSysDT 𝕄 n) (R₀ : S n) (U : S sys.m)
    (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ sys.m) (A : ℕ → Mat ℝ n n) (B : ℕ → Mat ℝ n sys.m) :
    Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  param (k : ℕ) : A k ∈ construct sys.A
  paramB (k : ℕ) : B k ∈ construct sys.B
  step (k : ℕ) : x (k + 1) = A k *ᵥ x k + B k *ᵥ u k + sys.c

/-- A run of the canonical form, its combined input `B u + c` in state coordinates drawn from
`U`. -/
structure LinParamSysDT.IsCanonicalTrajectory (sys : LinParamSysDT 𝕄 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : ∃ A ∈ construct sys.A, x (k + 1) = A *ᵥ x k + u k

/-- A canonical run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSysDT.IsCanonicalTrajectoryOn`'s are. -/
structure LinParamSysDT.IsCanonicalTrajectoryOn (sys : LinParamSysDT 𝕄 n) (R₀ U : S n) (K : ℕ)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : ∃ A ∈ construct sys.A, x (k + 1) = A *ᵥ x k + u k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
