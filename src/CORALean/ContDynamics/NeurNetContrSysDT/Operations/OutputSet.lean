module

public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.LinearSysDT.Operations.Basic
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic
public import CORALean.ContDynamics.OutputEq.Operations.OutputSet
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# The output set of a closed loop at a state set

`OutputEq.outputSet`'s `C R ⊕ D U ⊕ k` at the closed loop's input, which is two sets: the
controller's enclosure of its own output at `R`, through the first `m` columns of `D`, and the
external inputs `U_ext`, through the remaining ones, `D [a; e] = D_nn a + D_ext e`. With no external
input the second term is the zero set and this is `OutputEq.outputSet R (enclose R)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every output of the closed loop at a state of `R`, the network's output in its enclosure and
the external input in `U_ext`, enclosed: `C R ⊕ D_nn N(R) ⊕ D_ext U_ext ⊕ k`. -/
def NeurNetContrSysDT.outputSet (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) (R : S n) : S sys.plant.q :=
  plus (plus (mtimes sys.plant.outputEq.C R)
    (plus (mtimes (leftCols sys.hm sys.plant.outputEq.D) (sys.contr.enclose R))
      (mtimes (rightCols sys.hm sys.plant.outputEq.D) U_ext)))
    (OfScalarPoint.ofVec sys.plant.outputEq.k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
