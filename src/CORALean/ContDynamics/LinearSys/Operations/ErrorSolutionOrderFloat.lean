import CORALean.ContDynamics.LinearSys.Operations.ErrorEdgeFloat

/-!
# The order of the adaptive error solution, in floats

`errorSolutionOrder` computed in `𝕋`: CORA's loop of `errorSolution_adaptive`, raising `η`
from `2` until the gain `1 − former/edge` of the dominant edge `d` — the first coordinate of
longest edge at order `1`, as MATLAB's `max` takes it — falls below `ζ`, or that edge was `0`.
The edges are `errorEdgeFloat`'s, every comparison the float `le`, and `fuel` bounds the loop
CORA leaves open. A tuning selector: `errorSolutionAdaptiveFloat` is sound at any order. The
terms are those of [1, Prop. 11].

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The order `options.tt_err` CORA stores for a step, from `V`'s generators, in floats. -/
def LinearSys.errorSolutionOrderFloat (sys : LinearSys 𝕋 n) (ζ Δt : 𝕋) (V : Zonotope 𝕋 n)
    (fuel : ℕ) : Option ℕ :=
  let edge := sys.errorEdgeFloat Δt V                                -- RerrorInt_etanoF
  let crit := (List.finRange n).foldl (fun best d => match best with  -- [~,critDimnoF] = max(...)
    | none => some d
    | some b => if !le (edge 1 d) (edge 1 b) then some d else some b) none
  match crit with
  | none => none
  | some d => aux_errorSolutionOrderFloat ζ (fun η => edge η d) 2 fuel  -- loop from eta = 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
