module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSumFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Specification.STL.Operations.DepBloating

@[expose] public section

/-!
# The bloating `D`, over floats

[1, Eq. 14-20]: `D = (Σ_{j=1}^κ A^j Δt^{j+1}/(j+1)!) U₀ ⊕ ⨁_{j=1}^κ A^j Δt^{j+1}/(j+1)! U₀ ⊕
2Δt E U₀` with the bounds held in `𝕋`. The first term maps `U₀` by the interval matrix of the
sum (`MatExp.particularCoeffSum`), the second is the Minkowski sum of the `κ` images, one per `j`,
by the interval matrices `MatExp.intervalInputTerm`, and the third the symmetric interval matrix
`[-2Δt E, 2Δt E]` applied to `U₀` as CORA does for a symmetric matrix, the box `S · interval(U₀)`
(the reach `absBoundError` of `U₀` weighted by the radius), with `E` the scalar float bound
`MatExp.intervalInputRemainder` at the norm bound of `Δt A` where the exact layer takes the entries
of the remainder matrix. Soundness is `STL.depBloatingFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `U₀` – float input zonotope
* `Δt` – float time step
* `κ` – Taylor order

## Output
* the bloating float zonotope of the input set
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: the bloating `D` of `U₀`, rounded outward. -/
def STL.depBloatingFloat (A : Mat 𝕋 n n) (U₀ : Float.Zonotope (Vec 𝕋 n)) (Δt : 𝕋) (κ : ℕ) :
    Float.Zonotope (Vec 𝕋 n) :=
  -- `Σ_{j=1}^κ A^j Δt^{j+1}/(j+1)!` and its terms, as interval matrices over the point box `A`
  let first := Zonotope.mtimesIntervalMat (MatExp.particularCoeffSum (Interval.point A) Δt 1 κ) U₀
  let second := (List.range κ).foldl
    (fun Z j => Z.plus (Zonotope.mtimesIntervalMat (MatExp.intervalInputTerm (Interval.point A) Δt
      (j + 1)) U₀))
    (Zonotope.point (fun _ => zero))
  -- `E = [-2Δt E, 2Δt E]` applied as the box `E · interval(U₀)`
  let W := (MatExp.intervalInputRemainder (Interval.point A) Δt κ).sup
  let ρ : Vec 𝕋 n := fun i => sumUp fun k => mulUp (addUp (W i k) (W i k)) (U₀.absBoundError k)
  let third := Interval.zonotope (⟨-ρ, ρ⟩ : Interval (Vec 𝕋 n))
  (first.plus second).plus third

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
