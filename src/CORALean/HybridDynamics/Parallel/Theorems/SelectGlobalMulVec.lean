module

public import CORALean.HybridDynamics.Parallel.Operations.SelectGlobal

@[expose] public section

/-!
# What `selectGlobal` reads

`selectGlobal b` applied to a stacked vector `z` is, at global input `a`, the entry of `z` at the
first input bound to `a`, and `0` where no input is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {k m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.selectGlobal_mulVec {d q : Fin k → ℕ}
    (b : ∀ i, Fin (d i) → ResolveSource k q m) (z : Vec ℝ (∑ i, d i)) (a : Fin m) : -- --- CONCL ---
    (selectGlobal b *ᵥ z) a =
      if h : ∃ p', b (finSigmaFinEquiv.symm p').1 (finSigmaFinEquiv.symm p').2 = .global a then
        z (Fin.find _ h) else 0 := by -- --- PROOF ---
  -- one `1` in the row, at the first feeder, or none
  simp only [selectGlobal, Matrix.mulVec, dotProduct, Matrix.of_apply]
  split_ifs with h
  · simp [ite_mul, Finset.sum_ite_eq]
  · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
