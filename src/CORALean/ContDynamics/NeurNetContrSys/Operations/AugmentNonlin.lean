module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic
public import CORALean.ContDynamics.NonlinearSys.Instances

@[expose] public section

/-!
# The closed loop's augmented system at a nonlinear plant

CORA's `aux_computeProperties` at a `nonlinearSys`: the plant `ẋ = f(x, [a; e])` with the
network's output `a` as `m` further states of derivative zero and the external inputs `e` as the
inputs, `ż = [f(z₁, [z₂; e]); 0]` on the state `z = [x; a]`. A control period of the loop
([1, Alg. 2])
is a run of it.

## Inputs
* `sys` – closed-loop system

## Output
* the augmented nonlinear system over the state and the network output

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n M : ℕ} {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ż = [f(x, [a; e]); 0]` on `z = [x; a]` with the inputs `e`, in ℝ. -/
def NeurNetContrSys.augmentNonlin (sys : NeurNetContrSys (NonlinearSys n M) S n) :
    NonlinearSys (n + sys.m) sys.nExt where
  f z e := Fin.append (sys.plant.f (fun i => z (Fin.castAdd sys.m i))      -- f(x, [a; e])
    (joinInput sys.hm (fun j => z (Fin.natAdd n j)) e)) (fun _ => 0)       -- a' = 0
  q := 0
  g _ _ := fun i => i.elim0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
