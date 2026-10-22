module

public import CORALean.ContDynamics.OutputEq.OutputEq
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`, `ẋ = A x + B u + c + E w` with the output `y = C x + D u + k + F v`, every
matrix stored. The dimensions beside `n` are fields, as CORA's `nrOfInputs`, `nrOfOutputs`,
`nrOfDisturbances` and `nrOfNoises` are properties: `m`, `q`, `r`, `s`. `IsTrajectory` is a run of
the whole equation; `IsCanonicalTrajectory` is a run of CORA's `canonicalForm` [1], `ẋ = A x + u'`
with the combined input `u' = B u + c + E w`, the system [2, Sec. 2] states and what the
reachability algorithms are proved against (`IsTrajectory.canonical`). Both are Carathéodory runs,
the integral equation rather than a derivative at every point (Sontag, *Math. Control Theory*, Def.
C.2.1), as piecewise-continuous inputs jump; `meas` and `cont` are the regularity they need.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
* [2] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic
      Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.), Modeling, Design,
      and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A continuous-time linear system, as CORA's `linearSys`: matrices `A B C D E F` and offsets `c`,
`k`, with the input, output, disturbance and noise dimensions `m q r s` as fields. -/
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

/-- The output equation `y = C x + D u + k`, read off the system as stored; the noise term `F v`
stays with the system, as `OutputEq.outputSetNoise` takes `sys.F` beside it. -/
def LinearSys.outputEq (sys : LinearSys 𝕋 n) : OutputEq 𝕋 n sys.m sys.q :=
  ⟨sys.C, sys.D, sys.k⟩

/-- A Carathéodory run of the whole equation on `T`: the state from `X₀` under inputs in `U`
and disturbances in `W`, and the output under noise in `V`. -/
structure LinearSys.IsTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (X₀ : S n) (U : S sys.m)
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
  output (t : ℝ) (ht : t ∈ T) : y t = sys.outputEq.eval (x t) (u t) + toRealMat sys.F *ᵥ v t

/-- A Carathéodory run of `sys`'s canonical form on `T` from `R₀`, its combined input in state
coordinates drawn from `U`: `B`, `c` and `E` are already in `u`. -/
structure LinearSys.IsCanonicalTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
