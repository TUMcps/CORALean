module

public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.HybridDynamics.Operations.LinearResetResolveUpdate
public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `LinearReset.resolve`

CORA's `linearReset/resolve`: the reset `x ↦ A x + B u + c` of a parallel automaton, whose input
`u` stacks the inputs of all `k` components, becomes one whose input is the global input only.
For every input `j` of component `i` bound to the `l`-th output `y = C_c x_c + D_c u_c + q_c` of
component `c`, the column `B_part` of `B` feeds `y` back into `A`, `B` and `c`; the columns of
globally bound inputs are then summed per global index. Returns `(A, B, c)`. CORA's loop updates
`B` in place, but the columns it writes are global and the ones it reads are not, so the loop
equals the sum of the independent updates written here.

## Inputs
* `A` – state matrix
* `B` – stacked input matrix
* `c` – offset
* `C` – output matrices
* `D` – feedthrough matrices
* `q` – output offsets
* `stateBinds` – state index maps
* `inputBinds` – input bindings

## Output
* resolved matrices and offset
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

def LinearReset.resolve (A : Mat ℝ N N) (B : Mat ℝ N (∑ i, m i)) (c : Vec ℝ N)
    (C : ∀ i, Mat ℝ (p i) (n i)) (D : ∀ i, Mat ℝ (p i) (m i)) (q : ∀ i, Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    Mat ℝ N N × Mat ℝ N g × Vec ℝ N :=
  -- `idxCompInput{i}(j)`: the column of `u` that is input `j` of component `i`
  let idxCompInput : ∀ i, Fin (m i) → Fin (∑ i, m i) := fun i j => finSigmaFinEquiv ⟨i, j⟩
  -- the loop over the bound inputs
  let update := LinearReset.resolveUpdate B C D q stateBinds inputBinds
  let A' : Mat ℝ N N := A + ∑ ij, (update ij).1
  let B' : Mat ℝ N (∑ i, m i) := B + ∑ ij, (update ij).2.1
  let c' : Vec ℝ N := c + ∑ ij, (update ij).2.2
  -- `B(:,i) = sum(B(:,idx),2)` for the columns bound to global input `i`
  let Bglobal : Mat ℝ N g := Matrix.of fun a u =>
    ∑ ij : (Σ i, Fin (m i)),
      if inputBinds ij.1 ij.2 = .global u then B' a (idxCompInput ij.1 ij.2) else 0
  (A', Bglobal, c')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
