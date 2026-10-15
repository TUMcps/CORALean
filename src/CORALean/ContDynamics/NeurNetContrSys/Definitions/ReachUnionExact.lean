module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.NN.Operations.Eval

@[expose] public section

/-!
# The exact set `Reach NeurNetContrSys` is asked to enclose

Every state some zero-order-hold run over at most `H` periods of length `Δtc`
reaches, at a period boundary, run at the controller's own `eval` in place of a
free `π` — `NeurNetContrSys.Trajectory`'s fields, over a bare initial set, at any plant, the
disturbance in `W`; `Reach`'s instance takes `W = {0}`, as CORA's loop at a linear plant drops
the disturbance.
Positional, as the mathematics: `Reach` reads `Δtc` off the system, CORA's `sys.dt`,
and `H = tFinal - tStart` and the initial set off `params`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `H` periods of length `Δtc` of the closed loop
from a bare initial set `X`, under a disturbance in `W`, at a period boundary. -/
def NeurNetContrSys.reachUnionExact (sys : NeurNetContrSys P S n) (Δtc : ℝ) (H : ℕ)
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ i ≤ H, {y | ∃ x : ℝ → Vec ℝ n, ∃ w : ℝ → Vec ℝ (nrOfDisturbances sys.plant), x 0 ∈ X ∧
    (∀ j < H, ContDynamics.Trajectory sys.plant (Set.Icc 0 Δtc) Set.univ Set.univ W
      (fun t => x ((j : ℝ) * Δtc + t)) (fun _ => sys.contr.eval.out (x ((j : ℝ) * Δtc)))
      (fun t => w ((j : ℝ) * Δtc + t))) ∧
    x ((i : ℝ) * Δtc) = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
