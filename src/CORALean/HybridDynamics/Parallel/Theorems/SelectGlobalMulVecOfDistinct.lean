module

public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVec

@[expose] public section

/-!
# Where each global input feeds one input, `selectGlobal` reads that input

When no global input is bound to two inputs, the one input `⟨i, j⟩` bound to `a` is the first, so
`selectGlobal b` applied to `z` is `z ⟨i, j⟩` at `a`. This is the direction the exactness of a
lifted input set needs (`Lifting.Exact.input_inv`).

## Inputs
* `d` – input counts of the components
* `q` – output counts of the components
* `b` – input bindings
* `z` – stacked inputs
* `i` – component
* `j` – input of the component
* `a` – global input

## Hypotheses
* `hb` – no global input feeds two inputs
* `h` – the input is bound to `a`

## Conclusion
* the global input is the entry of that input
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

theorem ParallelHybridAutomaton.selectGlobal_mulVec_of_distinct {d q : Fin k → ℕ}
    {b : ∀ i, Fin (d i) → ResolveSource k q m}
    (hb : ∀ i i' j j' a, b i j = .global a → b i' j' = .global a →
      (⟨i, j⟩ : Σ i, Fin (d i)) = ⟨i', j'⟩)
    (z : Vec ℝ (∑ i, d i)) {i : Fin k} {j : Fin (d i)} {a : Fin m}
    (h : b i j = .global a) : -- --- CONCL ---
    (selectGlobal b *ᵥ z) a = z (finSigmaFinEquiv ⟨i, j⟩) := by -- --- PROOF ---
  have hex : ∃ p', b (finSigmaFinEquiv.symm p').1 (finSigmaFinEquiv.symm p').2 = .global a :=
    ⟨finSigmaFinEquiv ⟨i, j⟩, by
      rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩) = ⟨i, j⟩ from
        Equiv.symm_apply_apply _ _]
      exact h⟩
  rw [selectGlobal_mulVec, dif_pos hex]
  -- the first feeder is `⟨i, j⟩`, the only one
  have hp := hb _ _ _ _ a (Fin.find_spec hex) h
  congr 1
  rw [← Equiv.symm_apply_eq]
  exact hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
