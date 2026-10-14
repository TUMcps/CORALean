module

public import CORALean.ContDynamics.NeurNetContrSysNL.NeurNetContrSysNL

@[expose] public section

/-!
# The extended system of a control period

[1, Alg. 2], equation (4): the controller's output is constant over a period, so the closed loop
over it is `ż = (f(x, u, w), 0)` for `z = (x, u)`, a nonlinear system in the state `z` with the
disturbance `w` as input. Any reachability algorithm for nonlinear systems can then be run from the
initial set `X₀ × Y`, `Y` the image of `X₀` through the network.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2], equation (4): `ż = (f(x, u, w), 0)` on `z = (x, u)`. -/
def NeurNetContrSysNL.extended (sys : NeurNetContrSysNL S n m r) : NonlinearSys (n + m) r where
  f z w := Fin.append
    (sys.plant.f (fun k => z (Fin.castAdd m k))
      (Fin.append (fun k => z (Fin.natAdd n k)) w)) (0 : Vec ℝ m)
  q := sys.plant.q
  g z w := sys.plant.g (fun k => z (Fin.castAdd m k)) (Fin.append (fun k => z (Fin.natAdd n k)) w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
