module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ForcePropagation
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# What `forcePropagation` propagates

`forcePropagation` is `propagate` with the interval `stlInterval(0,inf)`, which denotes every time
`t ≥ 0`: every observation is final.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer

## Hypotheses
* none

## Conclusion
* it propagates over all times from zero
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.forcePropagation_spec (eps : ℝ) (obj : OnlineReachSetAnalyzer S d) :
    obj.forcePropagation eps = obj.propagate eps (STLInterval.stlInterval 0 ⊤ true true le_rfl) ∧
      (STLInterval.stlInterval 0 ⊤ true true le_rfl).set = Set.Ici 0 := by -- --- PROOF ---
  refine ⟨rfl, ?_⟩
  rw [STLInterval.set_stlInterval]
  ext t
  simp only [STLInterval.rawSet, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨h | ⟨-, h⟩, -⟩
    · exact_mod_cast h.le
    · exact_mod_cast h.le
  · intro h
    refine ⟨?_, Or.inl (EReal.coe_lt_top t)⟩
    rcases h.lt_or_eq with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr ⟨trivial, by rw [← h]; rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
