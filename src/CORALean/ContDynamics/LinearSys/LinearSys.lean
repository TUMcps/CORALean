module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`, `ẋ = A x + B u + c + E w` with the output `y = C x + D u + k + F v`, every
matrix stored. The dimensions beside `n` are fields, as CORA's `nrOfInputs`, `nrOfOutputs`,
`nrOfDisturbances` and `nrOfNoises` are properties: `m` inputs, `q` outputs, `r` disturbances,
`s` noises, the letters CORA's property comments use. `LinearSys 𝕋 n` is the type of every
system with `n` states, which is what `Reach` indexes a class by.

`Trajectory` is a run of the whole equation. `CanonicalTrajectory` is a run of CORA's
`canonicalForm` [1], `ẋ = A x + u'` with the combined input `u' = B u + c + E w` in state
coordinates, as in [2, Sec. 3.2]: what the reachability algorithms, which read `A` and an input
set in state coordinates, are proved against, as CORA's `reach` runs on `canonicalForm`.
`Trajectory.canonical` turns every run into one of those. Both are Carathéodory runs, stated
by the integral equation [2, Def. 3.1] writes, not by a derivative at every point: a
zero-order-hold input has none at a jump (Sontag, *Math. Control Theory*, Def. C.2.1). `meas`
is the input's own regularity, restricted to `T`; `cont` is Def. C.2.1's continuity, without
which `intervalIntegral`'s junk value would let `flow` admit an `x` nothing like a run.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSys (𝕋 : Type) (n : ℕ) where
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

/-- A Carathéodory run of the whole equation on `T`: the state from `X₀` under inputs in `U`
and disturbances in `W`, and the output under noise in `V`. -/
structure LinearSys.Trajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (X₀ : S n) (U : S sys.m)
    (W : S sys.r) (V : S sys.s) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ sys.m)
    (w : ℝ → Vec ℝ sys.r) (v : ℝ → Vec ℝ sys.s) (y : ℝ → Vec ℝ sys.q) : Prop where
  init : x 0 ∈ construct X₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  dist (t : ℝ) (ht : t ∈ T) : w t ∈ construct W
  noise (t : ℝ) (ht : t ∈ T) : v t ∈ construct V
  meas : AEStronglyMeasurable u (volume.restrict T)
  measDist : AEStronglyMeasurable w (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t,
    (toRealMat sys.A *ᵥ x s + toRealMat sys.B *ᵥ u s + toRealVec sys.c + toRealMat sys.E *ᵥ w s)
  output (t : ℝ) (ht : t ∈ T) :
    y t = toRealMat sys.C *ᵥ x t + toRealMat sys.D *ᵥ u t + toRealVec sys.k + toRealMat sys.F *ᵥ v t

/-- A Carathéodory run of `sys`'s canonical form on `T` from `R₀`, its combined input in state
coordinates drawn from `U`: `B`, `c` and `E` are already in `u`. -/
structure LinearSys.CanonicalTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
