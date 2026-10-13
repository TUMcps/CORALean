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
`u` stacks the inputs of all `k` components (component `i` has `m i`, in `idxCompInput`), is turned
into one whose input is the global input only. For every input `j` of component `i` bound to the
`l`-th output `y = C_c x_c + D_c u_c + q_c` of component `c`, the column `B_part` of `B` at the
states of `i` feeds `y` back: `A(stateBinds{i}, stateBinds{c}) += B_part C(l,:)`,
`B(stateBinds{i}, idxCompInput{c}) += B_part D(l,:)`, `c(stateBinds{i}) += B_part q(l)`. The columns
of `B` of the globally bound inputs are then summed per global index. Returns `(A, B, c)`.

CORA's loop updates `B` in place; the columns it writes (the inputs `D(l,:)` points at) are
global ones, which `resolve` throws for if they are not, and the columns it reads (`B_part`) are
non-global ones, so the loop equals the sum of the independent updates written here.
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
