module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The augmented linear system of a control period

CORA's `aux_augmentLinear`: the extended system (`extended`) of a linear plant is linear again,
the state `[x; u]` under `[A B; 0 0]` with the offset `[c; 0]` — the network's output is a state
whose derivative is zero. One input column of zeros, CORA's `B_aug = zeros(n+m, 1)`: the network
drives every input, so there are no external inputs left. Read in ℝ, so that `LinearSys`'s exact
reachability runs on it; `augmentFloat` is the same matrices in the plant's scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[A B; 0 0]` and `[c; 0]` on the state `[x; u]`, in ℝ. -/
def NeurNetContrSys.augment (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) :
    LinearSys ℝ (n + sys.plant.m) where
  m := 1
  q := 0
  r := 0
  s := 0
  A := Matrix.of (Fin.append (fun i => Fin.append (toRealMat sys.plant.A i)  -- [A B; 0 0]
    (toRealMat sys.plant.B i)) (fun _ _ => 0))
  B := 0                                                            -- zeros(n+m, 1)
  c := Fin.append (toRealVec sys.plant.c) 0                         -- [c; 0]
  C := 0
  D := 0
  k := 0
  E := 0
  F := 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
