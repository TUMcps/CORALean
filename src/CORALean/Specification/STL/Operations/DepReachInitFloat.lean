module

public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Specification.STL.Definitions.DepReachConstsFloat
public import CORALean.Specification.STL.Definitions.DepReachStateFloat
public import CORALean.Specification.STL.Operations.DepBoxFloat
public import CORALean.Specification.STL.Operations.DepReachInit

@[expose] public section

/-!
# Lines 2-3 of the dependency preserving reachability algorithm, over floats

[1, Alg. 1], lines 2-3 with the sets held in `𝕋`: `H(t₀) = X₀`, `P_c(t₀) = D₀ = 0` as point
zonotopes, and `C₀ ← interval(F X₀ ⊕ G ũ)` with the float `mtimesIntervalMat` and `depBoxFloat`.
Soundness is `STL.depReachInitFloat_outer`.

## Inputs
* `X₀` – float initial set
* `cs` – float constants of the algorithm

## Output
* the float algorithm state at time zero
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

/-- Lines 2-3 of [1, Alg. 1] in `𝕋`: the state at `t₀ = 0`. -/
def STL.depReachInitFloat (X₀ : Float.Zonotope (Vec 𝕋 n)) (cs : STL.DepReachConstsFloat 𝕋 n) :
    STL.DepReachStateFloat 𝕋 n :=
  -- 2. `H(t₀) ← X₀`
  let H₀ := X₀
  -- 2. `P_c(t₀) ← 0`
  let Pc₀ : Float.Zonotope (Vec 𝕋 n) := Zonotope.point (fun _ => zero)
  -- 2. `D₀ ← 0`
  let D₀ : Float.Zonotope (Vec 𝕋 n) := Zonotope.point (fun _ => zero)
  -- 3. `C₀ ← interval(F X₀ ⊕ G ũ)`
  let C₀ := STL.depBoxFloat ((Zonotope.mtimesIntervalMat cs.F X₀).plus
    (Zonotope.mtimesIntervalMat cs.G cs.ũ))
  ⟨H₀, Pc₀, D₀, C₀⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
