module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Continuous-time linear systems with a set-valued system matrix

CORA's `@linParamSys`, `ẋ(t) = A x(t) + B u(t) + c` with `A` ranging over a set `sys.A` — the
system-matrix uncertainty CORA calls `type` — and `B`, `c` plain, as CORA's are; `m` inputs, a
field as in `LinearSys`. `Trajectory` is `'varParam'`, a fresh `A t ∈ construct sys.A` at every
instant; `ConstTrajectory` is `'constParam'` (CORA's default), one `A ∈ construct sys.A` over the
whole flow. Both are Carathéodory runs, as `LinearSys.Trajectory` is: the integral equation
[1, Def. 3.1] writes, with the parameter inside the integral, so a jumping input or parameter is
admissible; `meas` and `measParam` make the input and the parameter measurable on `T`.
`CanonicalTrajectory` and `CanonicalConstTrajectory` are the same runs of the canonical form
`ẋ = A x + u'`, the combined input `u' = B u + c` in state coordinates, which is what the
reachability algorithms read and are proved against; `Trajectory.canonical` and
`ConstTrajectory.canonical` turn every run into one. `constTrajectory_toTrajectory` is
the direction between the canonical readings that always holds; the converse fails
    (a run free to vary
need not settle on one matrix) and is not stated.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinParamSys (𝕄 : ℕ → ℕ → Type) (n : ℕ) where
  A : 𝕄 n n
  m : ℕ
  B : Mat ℝ n m
  c : Vec ℝ n

/-- `'varParam'`: a fresh `A t ∈ construct sys.A` at every instant, under inputs in `U`. -/
structure LinParamSys.Trajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (X₀ : S n) (U : S sys.m)
    (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ sys.m) (A : ℝ → Mat ℝ n n) : Prop where
  init : x 0 ∈ construct X₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : A t ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  measParam : AEStronglyMeasurable A (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A s *ᵥ x s + sys.B *ᵥ u s + sys.c)

/-- `'constParam'`: one matrix `A`, fixed over the whole flow, under inputs in `U`. -/
structure LinParamSys.ConstTrajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (X₀ : S n)
    (U : S sys.m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ sys.m) (A : Mat ℝ n n) : Prop where
  init : x 0 ∈ construct X₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : A ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A *ᵥ x s + sys.B *ᵥ u s + sys.c)

/-- `'varParam'` of the canonical form, its combined input in state coordinates drawn from `U`. -/
structure LinParamSys.CanonicalTrajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : ℝ → Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : A t ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  measParam : AEStronglyMeasurable A (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A s *ᵥ x s + u s)

/-- `'constParam'` of the canonical form: one matrix `A`, rather than `CanonicalTrajectory`'s
fresh `A t` at each instant. -/
structure LinParamSys.CanonicalConstTrajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : A ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
