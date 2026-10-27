module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# The order of the adaptive error solution, in floats

`errorSolutionOrder` computed in `𝕋`: CORA's loop of `errorSolution_adaptive`, raising `η`
from `2` until the gain `1 − former/edge` of the dominant edge `d` — the first coordinate of
longest edge at order `1`, as MATLAB's `max` takes it — falls below `ζ`, or that edge was `0`.
The edges are `aux_errorEdgeFloat`'s, every comparison the float `le`, and `fuel` bounds the loop
CORA leaves open. A tuning selector: `errorSolutionAdaptiveFloat` is sound at any order. The
terms are those of [1, Prop. 11].

## Inputs
* `sys` – linear system
* `ζ` – float gain threshold
* `Δt` – float step length
* `V` – float noise zonotope
* `fuel` – number of orders tried

## Output
* order CORA stores for the step, if found

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop from order `η` on: `edge η` is the dominant edge at `η`, one step older the
`former` one. -/
def aux_errorSolutionOrderFloat (ζ : 𝕋) (edge : ℕ → 𝕋) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | η, fuel + 1 =>
    let gain := subDown one (divUp (edge (η - 1)) (edge η))          -- 1 - former / edge
    if (!le ζ gain || le (edge (η - 1)) zero) = true then some η      -- gain < ζ, or edge 0
    else aux_errorSolutionOrderFloat ζ edge (η + 1) fuel

/-- The edge length of the generator sum, per coordinate, up to order `η`, rounded up. -/
def LinearSys.aux_errorEdgeFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (V : Zonotope (Vec 𝕋 n)) (η : ℕ) :
    Vec 𝕋 n :=
  let Ã := fun i : Fin (η + 1) => MatExp.intervalInputTerm (Interval.point sys.A) Δt i  -- [Ãᵢ]
  fun d => sumUp fun i : Fin (η + 1) => sumUp fun j : Fin V.h =>      -- Σᵢ Σⱼ
    sumUp fun k => mulUp (maximum (absolute ((Ã i).inf d k)) (absolute ((Ã i).sup d k)))
      (absolute (V.G j k))                                             -- ≥ |(Ãᵢ G_j)_d|


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The order `options.tt_err` CORA stores for a step, from `V`'s generators, in floats. -/
def LinearSys.errorSolutionOrderFloat (sys : LinearSys 𝕋 n) (ζ Δt : 𝕋) (V : Zonotope (Vec 𝕋 n))
    (fuel : ℕ) : Option ℕ :=
  let edge := sys.aux_errorEdgeFloat Δt V                                -- RerrorInt_etanoF
  let crit := (List.finRange n).foldl (fun best d => match best with  -- [~,critDimnoF] = max(...)
    | none => some d
    | some b => if !le (edge 1 d) (edge 1 b) then some d else some b) none
  match crit with
  | none => none
  | some d => aux_errorSolutionOrderFloat ζ (fun η => edge η d) 2 fuel  -- loop from eta = 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
