module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The extended system of a control period

[1, Alg. 2], equation (4), and CORA's `aux_computeProperties`: the controller's output is
constant over a period, so the closed loop over it is `ż = (f(x, u, w), 0)` for `z = (x, u)`, a
nonlinear system in the state `z` with the disturbance `w` as input — CORA's
`f = @(x,u) [sys.mFile(x(1:n), [x(n+1:n+m); u]); zeros(m, 1)]`, at whichever plant. Any
reachability algorithm for it can then be run from the initial set `X₀ × Y`, `Y` the image of
`X₀` through the network. No output equation: CORA's closed loop drops it, and the loop never
reads it.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open NeurNetContrSys (Plant)

variable {n : ℕ} {P : Type} [Plant P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1], equation (4) of the reach algorithm: `ż = (f(x, u, w), 0)` on `z = (x, u)`. -/
def NeurNetContrSys.extended (sys : NeurNetContrSys P S n) :
    NonlinearSys (n + Plant.m sys.plant) (Plant.r sys.plant) where
  f z w := Fin.append
    (Plant.f sys.plant (fun k => z (Fin.castAdd _ k)) (fun k => z (Fin.natAdd n k)) w)
    (0 : Vec ℝ (Plant.m sys.plant))
  q := 0
  g _ _ := 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
