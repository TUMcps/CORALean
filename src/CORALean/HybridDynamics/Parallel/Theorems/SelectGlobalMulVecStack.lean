module

public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVec
public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# `selectGlobal` recovers the global inputs from inputs that agree with them

If every input bound to global input `a` is `g a`, and `g` is zero at the global inputs no input
reads, then `selectGlobal b` takes the stack of the inputs to `g`: each row reads one input bound
to its global input, whichever it is. So the image of the product of the components' input sets
holds every global-input vector the components admit (`Lifting.mem_input`).
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

theorem ParallelHybridAutomaton.selectGlobal_mulVec_stack {d q : Fin k → ℕ}
    (b : ∀ i, Fin (d i) → ResolveSource k q m) (v : ∀ i, Vec ℝ (d i)) (g : Vec ℝ m)
    (hv : ∀ i j a, b i j = .global a → v i j = g a)
    (hz : ∀ a, (∀ i j, b i j ≠ .global a) → g a = 0) : -- --- STMT ---
    selectGlobal b *ᵥ stack v = g := by -- --- PROOF ---
  funext a
  rw [selectGlobal_mulVec]
  split_ifs with h
  · -- the first feeder is an input bound to `a`
    exact hv _ _ a (Fin.find_spec h)
  · -- no input reads `a`
    refine (hz a fun i j hij => h ⟨finSigmaFinEquiv ⟨i, j⟩, ?_⟩).symm
    rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩) = ⟨i, j⟩ from
      Equiv.symm_apply_apply _ _]
    exact hij

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
