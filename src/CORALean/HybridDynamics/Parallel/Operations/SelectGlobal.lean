module

public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `selectGlobal`: the global inputs, read off the stacked inputs

The matrix from the stacked inputs of the components, `Vec ℝ (∑ i, d i)`, to the global inputs:
row `a` picks the first input that `b` binds to global input `a` (in the order of the stack), and
is zero where none is. CORA's `aux_mergeInputSet` places each component's input set at its global
inputs by `projectHighDim`; this is the same placement read backwards, so that the image of the
product of the components' input sets is the product's input set (`zonoLifting`, ...).
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `a`: a `1` at the first stacked input bound to global input `a`, zeros elsewhere. -/
def ParallelHybridAutomaton.selectGlobal {d q : Fin k → ℕ}
    (b : ∀ i, Fin (d i) → ResolveSource k q m) : Mat ℝ m (∑ i, d i) :=
  Matrix.of fun a p =>
    if h : ∃ p', b (finSigmaFinEquiv.symm p').1 (finSigmaFinEquiv.symm p').2 = .global a then
      (if Fin.find _ h = p then 1 else 0)
    else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
