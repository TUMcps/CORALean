import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.NN.Operations.Enclose

/-!
# A network in the loop: reachability

The alternation and nothing else: run the controller over the current
enclosure to enclose the inputs it can produce there, and hand that to the
plant as one step's input set. Both halves are already written, so this file
computes nothing new — one step of `LinearSysDT.reach` is the step and
`NeuralNetwork.enclose` is the input set it takes.

The precision is lost in one place, and it is worth naming. `enclose` runs on
the same set the step is taken from and `plus` combines the two, so every state
in the enclosure is paired with every input in it, not with the input the
controller produces at that state. No order bound recovers the difference.

`ρ` is uniform across steps, as in `LinearSysDT.reach`, and time is
counted in sampling periods (`ℕ`) with `tFinal - tStart` steps, as there; a
`Reach.Params`, since the controller, not the caller, supplies the inputs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set of the closed loop at time `tFinal`, from `R₀` at `tStart`,
held at maximum order `ρ`. -/
def NeurNetContrSysDT.reach (sys : NeurNetContrSysDT 𝕋 S n) (params : Reach.Params (S n) ℕ)
    (options : NeurNetContrSysDT.ReachOptions) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let o := options.ρ
  let ho := options.hZonotopeOrder
  let step := fun R =>                                              -- plant on the enclosed inputs
    sys.plant.reach ⟨R, sys.contr.enclose R, 0, 1⟩ ⟨o, ho⟩
  Nat.repeat step N R₀                                              -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
