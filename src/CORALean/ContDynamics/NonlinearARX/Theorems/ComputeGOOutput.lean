module

public import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGO
public import CORALean.ContDynamics.NonlinearARX.Theorems.OutputSelMulVec
public import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOOutput
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# `computeGO` gives the output of every ARX run

`y(k) - y_ref(k)` is `C{k}` applied to the initial window's deviation, plus `D{k,j}` applied
to each stacked-input deviation, plus `E{k,j}` applied to each linearization error
`L_j = [L_x; L_y]` (here `L_y = 0`, the output being linear), for every run of the ARX system.
An identity, as for `NonlinearSysDT`: the errors are the `linResidual`s of the converted
system, not bounded. `0 < p`, as the output is a block of the window. The source is [1].

## References

* [1] `contDynamics/@nonlinearARX/computeGO.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.computeGO_output (sys : NonlinearARX dy du p) (hp : 0 < p)
    (x0 : Vec ℝ (p * dy)) (u_ref : ℕ → Vec ℝ du) {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du}
    (hy : ∀ k, p ≤ k → y k = sys.f (NonlinearARX.pastOut p y k) (NonlinearARX.pastIn p u k))
    (k : ℕ) : -- --- STMT ---
    y k - (sys.computeGO x0 u_ref).y k
      = (sys.computeGO x0 u_ref).C k *ᵥ (NonlinearARX.stack p y 0 - x0)
        + ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).D k j *ᵥ
            (NonlinearARX.feed p u j - NonlinearARX.feed p u_ref j)
        + ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).E k j *ᵥ
            (Fin.append
              (linResidual sys.toNonlinearSysDT.f ((sys.computeGO x0 u_ref).x j)
                (NonlinearARX.feed p u_ref j) (NonlinearARX.stack p y j) (NonlinearARX.feed p u j))
              (linResidual (fun x (_ : Vec ℝ ((p + 1) * du)) => sys.outputSel (𝕋 := ℝ) *ᵥ x)
                ((sys.computeGO x0 u_ref).x j) (NonlinearARX.feed p u_ref j)
                (NonlinearARX.stack p y j) (NonlinearARX.feed p u j))
              : Vec ℝ (p * dy + dy)) := by -- --- PROOF ---
  -- the windows are a run of the converted system
  have h := NonlinearSysDT.computeGO_output
    { sys.toNonlinearSysDT with q := dy, g := fun x _ => sys.outputSel (𝕋 := ℝ) *ᵥ x } x0
    (NonlinearARX.feed p u_ref) (x := NonlinearARX.stack p y) (u := NonlinearARX.feed p u)
    (fun k => sys.toNonlinearSysDT_step hy k) k
  -- and the selection matrix reads `y(k)` off the window
  have hsel : sys.outputSel (𝕋 := ℝ) *ᵥ NonlinearARX.stack p y k = y k :=
    sys.outputSel_mulVec (𝕋 := ℝ) hp y k
  rw [← hsel]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
