import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.NN.Operations.Enclose

/-!
# A network in the loop: reachability

The alternation and nothing else: run the controller over the current
enclosure to enclose the inputs it can produce there, and hand that to the
plant as one step's input set. Both halves are already written, so this file
computes nothing new — `LinearSysDT.reach ... 1` is the step and
`NeuralNetwork.enclose` is the input set it takes.

The precision is lost in one place, and it is worth naming. `enclose` runs on
the same set the step is taken from and `plus` combines the two, so every state
in the enclosure is paired with every input in it, not with the input the
controller produces at that state. No order bound recovers the difference.

`o` is uniform across steps, as in `LinearSysDT.reach`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set of the closed loop after `k` steps, from `R₀`, held at
maximum order `o`. `ho` is what rules out `o = 0`. -/
def NeurNetContrSysDT.reach (sys : NeurNetContrSysDT 𝕋 S n) (o : ℕ) (ho : 0 < o) (R₀ : S n) :
    ℕ → S n
  | 0 => R₀
  | k + 1 => sys.plant.reach o ho (sys.reach o ho R₀ k)
      (sys.contr.enclose (sys.reach o ho R₀ k)) 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
