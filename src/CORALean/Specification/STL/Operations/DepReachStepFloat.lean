module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachConstsFloat
public import CORALean.Specification.STL.Definitions.DepReachStateFloat
public import CORALean.Specification.STL.Operations.DepBoxFloat
public import CORALean.Specification.STL.Operations.DepReachStep

@[expose] public section

/-!
# Lines 5-7 of the dependency preserving reachability algorithm, over floats

[1, Alg. 1], one pass of the loop with the sets held in `𝕋`. The real `e^{AΔt}` is the float
interval matrix `MatExp.expIntervalEnclosure` of the point box `Δt A` at order `η`, applied to each
set by `Zonotope.mtimesIntervalMat`; `T ũ` and `T U₀` apply the interval matrix `T` and `D_{i+1}`
is boxed by `depBoxFloat`. Soundness is `STL.depReachStepFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `η` – Taylor order of the matrix exponential
* `cs` – float constants of the algorithm
* `s` – float algorithm state

## Output
* the float algorithm state one step later
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-7 of [1, Alg. 1] in `𝕋`. -/
def STL.depReachStepFloat (A : Mat 𝕋 n n) (Δt : 𝕋) (η : ℕ) (cs : STL.DepReachConstsFloat 𝕋 n)
    (s : STL.DepReachStateFloat 𝕋 n) : STL.DepReachStateFloat 𝕋 n :=
  -- 5. `e^{AΔt}`, which lines 5-7 apply to every set
  let Φ := MatExp.expIntervalEnclosure (Interval.smul Δt Δt (Interval.point A)) η
  -- 5. `C_{i+1} ← e^{AΔt} C_i`
  let C' := Zonotope.mtimesIntervalMat Φ s.C
  -- 6. `H(t_{i+1}) ← e^{AΔt} H(t_i) ⊕ T ũ`
  let H' := (Zonotope.mtimesIntervalMat Φ s.H).plus (Zonotope.mtimesIntervalMat cs.T cs.ũ)
  -- 6. `D_{i+1} ← interval(e^{AΔt} D_i ⊕ D)`
  let D' := STL.depBoxFloat ((Zonotope.mtimesIntervalMat Φ s.D).plus cs.D)
  -- 7. `P_c(t_{i+1}) ← e^{AΔt} P_c(t_i) ⊕ T U₀`
  let Pc' := (Zonotope.mtimesIntervalMat Φ s.Pc).plus (Zonotope.mtimesIntervalMat cs.T cs.U₀)
  ⟨H', Pc', D', C'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
