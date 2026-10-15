module

public import CORALean.ContDynamics.LinearSys.Instances
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The augmented linear system of a control period

CORA's `aux_augmentLinear`: the extended system of a linear plant is linear again, the state `[x;
u_nn]` under `[A B_nn; 0 0]` with the input matrix `[B_ext; 0]` and the offset `[c; 0]` — the
network's output is a state whose derivative is zero, and the external inputs `u_ext` stay inputs,
`x' = A x + B_nn u_nn + B_ext u_ext + c`. `B_nn` and `B_ext` are the first `m` and the remaining
columns of `B` (`leftCols`, `rightCols`). CORA gives the system a dummy zero column when there are
no external inputs (`B_aug = zeros(n+m, 1)`, `n_ext = max(1, …)`), as a MATLAB system needs an input
dimension; here the input dimension is `nExt` itself, `0` then, and the reach sets are the same, the
dummy column being zero. Read in ℝ, so that `LinearSys`'s exact reachability runs on it;
`augmentFloat` is the same matrices in the plant's scalar.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[A B_nn; 0 0]`, `[B_ext; 0]` and `[c; 0]` on the state `[x; u_nn]`, in ℝ. -/
def NeurNetContrSys.augment (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) :
    LinearSys ℝ (n + sys.m) where
  m := sys.nExt
  q := 0
  r := 0
  s := 0
  A := Matrix.of (Fin.append (fun i => Fin.append (toRealMat sys.plant.A i)  -- [A B_nn; 0 0]
    (leftCols sys.hm (toRealMat sys.plant.B) i)) (fun _ _ => 0))
  B := Matrix.of (Fin.append (fun i => rightCols sys.hm (toRealMat sys.plant.B) i)  -- [B_ext; 0]
    (fun _ _ => 0))
  c := Fin.append (toRealVec sys.plant.c) 0                         -- [c; 0]
  C := 0
  D := 0
  k := 0
  E := 0
  F := 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
