module

public import CORALean.ContDynamics.LinearSys.Instances
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The augmented linear system of a control period, in the plant's scalar

`augment` with its matrices kept in the scalar `𝕋` the plant is stored in, so that the float
reachability of `LinearSys` (`discretizeEnclosureFloat`, `inputSolutionFloat`) runs on it: CORA's
`aux_augmentLinear`, `[A B_nn; 0 0]`, `[B_ext; 0]` and `[c; 0]`, the zeros being `𝕋`'s own. It reads
as `augment` entry by entry (`toRealMat_augmentFloat`).
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[A B_nn; 0 0]`, `[B_ext; 0]` and `[c; 0]` on the state `[x; u_nn]`, in `𝕋`. -/
def NeurNetContrSys.augmentFloat (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) :
    LinearSys 𝕋 (n + sys.m) where
  m := sys.nExt
  q := 0
  r := 0
  s := 0
  A := Matrix.of (Fin.append (fun i => Fin.append (sys.plant.A i)  -- [A B_nn; 0 0]
    (leftCols sys.hm sys.plant.B i))
    (fun _ _ => zero))
  B := Matrix.of (Fin.append (fun i => rightCols sys.hm sys.plant.B i)  -- [B_ext; 0]
    (fun _ _ => zero))
  c := Fin.append sys.plant.c (fun _ => zero)                       -- [c; 0]
  C := fun i => i.elim0
  D := fun i => i.elim0
  k := fun i => i.elim0
  E := fun _ j => j.elim0
  F := fun i => i.elim0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
