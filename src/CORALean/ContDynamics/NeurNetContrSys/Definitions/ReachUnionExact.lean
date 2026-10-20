module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.NN.Operations.Eval

@[expose] public section

/-!
# The exact set `Reach NeurNetContrSys` is asked to enclose

Every state some zero-order-hold run over at most `H` periods of length `sys.dt`
reaches, at a period boundary, run at the controller's own `eval` in place of a
free `π` — `NeurNetContrSys.IsTrajectory`'s fields, over a bare initial set, at any plant, the
external input in `U_ext` and the disturbance in `W`; `Reach`'s instance takes `W = {0}`, as
CORA's loop at a linear plant drops the disturbance.
Positional, as the mathematics: `Reach` reads `sys.dt` off the system, as CORA does,
and `H = tFinal - tStart` and the initial set off `params`.

## Inputs
* `sys` – closed-loop system
* `H` – number of periods
* `U_ext` – external input set
* `W` – disturbance set
* `X` – initial set

## Output
* the states some closed-loop run is at a period boundary within `H` periods
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `H` periods of length `sys.dt` of the closed loop
from a bare initial set `X`, under an external input in `U_ext` and a disturbance in `W`, at a
period boundary. -/
def NeurNetContrSys.reachUnionExact (sys : NeurNetContrSys P S n) (H : ℕ)
    (U_ext : Set (Vec ℝ sys.nExt)) (W : Set (Vec ℝ (nrOfDisturbances sys.plant)))
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ i ≤ H, {y | ∃ x : ℝ → Vec ℝ n, ∃ v : ℝ → Vec ℝ sys.nExt,
    ∃ w : ℝ → Vec ℝ (nrOfDisturbances sys.plant), x 0 ∈ X ∧
    (∀ j < H, ContDynamics.IsTrajectory sys.plant (Set.Icc 0 sys.dt) Set.univ
      (sys.inputSet {sys.contr.eval.out (x ((j : ℝ) * sys.dt))} U_ext) W
      (fun t => x ((j : ℝ) * sys.dt + t))
      (fun t => sys.input (sys.contr.eval.out (x ((j : ℝ) * sys.dt))) (v ((j : ℝ) * sys.dt + t)))
      (fun t => w ((j : ℝ) * sys.dt + t))) ∧
    x ((i : ℝ) * sys.dt) = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
