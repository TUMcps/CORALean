module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# A network in the loop: reachability

The alternation and nothing else: run the controller over the current
enclosure to enclose the inputs it can produce there, map them by the plant's `B` and add its
`c`, and hand `B N(R) ⊕ c` to the plant as one step's input set, so a step is
`reduce(A R ⊕ B N(R) ⊕ c)`, CORA's step of the augmented `[x; u]`. Both halves are already
written: one step of `LinearSysDT.reach` is the step and `NeuralNetwork.enclose` the input set
it maps.

The precision is lost in one place, and it is worth naming. `enclose` runs on
the same set the step is taken from and `plus` combines the two, so every state
in the enclosure is paired with every input in it, not with the input the
controller produces at that state. No order bound recovers the difference.

`ρ` is uniform across steps, as in `LinearSysDT.reach`, and time is
counted in sampling periods (`ℕ`) with `tFinal - tStart` steps, as there; a
`Reach.Params`, since the controller, not the caller, supplies the inputs.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set of the closed loop at time `tFinal`, from `R₀` at `tStart`,
held at maximum order `ρ`. -/
def NeurNetContrSysDT.reach (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n) (params : Reach.Params
    (S n) ℕ)
    (options : NeurNetContrSysDT.ReachOptions) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let o := options.ρ
  let ho := options.hZonotopeOrder
  let step := fun R =>                                              -- one closed-loop step from R
    let U := plus (mtimes sys.plant.B (sys.contr.enclose R))        -- B N(R) ⊕ c, the input
      (OfScalarPoint.ofVec sys.plant.c)
    sys.plant.reach ⟨R, U, 0, 1⟩ ⟨o, ho⟩                           -- A R ⊕ B N(R) ⊕ c, reduced
  Nat.repeat step N R₀                                              -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
