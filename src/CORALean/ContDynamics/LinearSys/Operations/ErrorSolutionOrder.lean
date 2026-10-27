module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The order of the adaptive error solution

CORA's loop of `errorSolution_adaptive`: raise `η` from `2` until the gain `1 − former/edge`
of the dominant edge `d`, the coordinate of the longest edge at order `1`, falls below
`ζ` (`options.zetaTabs`) or that edge was `0`. Neither `Nat.find` nor `Classical.choose`:
the comparisons go through the caller's `lt`, `fuel` bounds the loop CORA leaves open,
and `none` is a loop out of fuel. The first coordinate of maximal edge is taken, as
MATLAB's `max` does. The terms are those of [1, Prop. 11].

## Inputs
* `sys` – linear system
* `lt` – strict comparison oracle on reals
* `ζ` – gain threshold
* `Δt` – step length
* `V` – noise zonotope
* `fuel` – number of orders tried

## Output
* order CORA stores for the step, if found

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The loop from order `η` on: `edge η` is the dominant edge at `η`, one step older the
`former` one. -/
@[step_of LinearSys.errorSolutionOrder]
noncomputable def step_errorSolutionOrder (lt : ℝ → ℝ → Bool) (ζ : ℝ) (edge : ℕ → ℝ) :
    ℕ → ℕ → Option ℕ
  | _, 0 => none
  | η, fuel + 1 =>
    if (lt (1 - edge (η - 1) / edge η) ζ || !lt 0 (edge (η - 1))) = true then some η
    else step_errorSolutionOrder lt ζ edge (η + 1) fuel

/-- The edge length of the generator sum, per coordinate, up to order `η`. -/
@[step_of LinearSys.errorSolutionOrder]
noncomputable def LinearSys.step_errorEdge (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (V : Zonotope (Vec ℝ n)) (η : ℕ) : Vec ℝ n :=
  fun d => ∑ i ∈ Finset.range (η + 1), ∑ j, |(MatExp.particularCoeff (toRealMat sys.A) Δt i
    *ᵥ V.G j) d|


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The order `options.tt_err` CORA stores for a step, from `V`'s generators. -/
noncomputable def LinearSys.errorSolutionOrder (sys : LinearSys 𝕋 n) (lt : ℝ → ℝ → Bool)
    (ζ Δt : ℝ) (V : Zonotope (Vec ℝ n)) (fuel : ℕ) : Option ℕ :=
  let edge := sys.step_errorEdge Δt V                                     -- RerrorInt_etanoF
  let crit := (List.finRange n).foldl (fun best d => match best with  -- [~,critDimnoF] = max(...)
    | none => some d
    | some b => if lt (edge 1 b) (edge 1 d) then some d else some b) none
  match crit with
  | none => none
  | some d => step_errorSolutionOrder lt ζ (fun η => edge η d) 2 fuel -- loop from eta = 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
