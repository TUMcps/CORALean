module

public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `LinearReset.resolveUpdate`

The three updates `(A, B, c) += (BC_j, BD_j, Bq_j)` of the loop body of CORA's
`linearReset/resolve`: input `j` of component `i`, bound to the `l`-th output of component `c`,
feeds `y = C_c x_c + D_c u_c + q_c` back through the column `B_part` of `B` at the states of `i`.
Zero for a globally bound input.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearReset.resolveUpdate (B : Mat ℝ N (∑ i, m i))
    (C : ∀ i, Mat ℝ (p i) (n i)) (D : ∀ i, Mat ℝ (p i) (m i)) (q : ∀ i, Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (ij : Σ i, Fin (m i)) : Mat ℝ N N × Mat ℝ N (∑ i, m i) × Vec ℝ N :=
  -- `idxCompInput{i}(j)`: the column of `u` that is input `j` of component `i`
  let idxCompInput : ∀ i, Fin (m i) → Fin (∑ i, m i) := fun i j => finSigmaFinEquiv ⟨i, j⟩
  match inputBinds ij.1 ij.2 with
  | .global _ => (0, 0, 0)
  | .output c' l =>
    -- `B_part = B(stateBinds{i}, idxCompInput{i}(j))`
    let Bpart : Fin N → ℝ :=
      scatter (stateBinds ij.1) (fun r => B (stateBinds ij.1 r) (idxCompInput ij.1 ij.2))
    -- `BC_j = B_part * C(l,:)`, added at `A(stateBinds{i}, stateBinds{c})`
    let BCj : Mat ℝ N N := Matrix.vecMulVec Bpart (scatter (stateBinds c') (fun s => C c' l s))
    -- `BD_j = B_part * D(l,:)`, added at `B(stateBinds{i}, idxCompInput{c})`
    let BDj : Mat ℝ N (∑ i, m i) :=
      Matrix.vecMulVec Bpart (fun col => ∑ jj, if col = idxCompInput c' jj then D c' l jj else 0)
    -- `Bq_j = B_part * q(l)`, added at `c(stateBinds{i})`
    let Bqj : Vec ℝ N := fun a => Bpart a * q c' l
    (BCj, BDj, Bqj)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
