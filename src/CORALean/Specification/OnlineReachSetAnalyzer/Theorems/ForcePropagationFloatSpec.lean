module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ForcePropagationFloat
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# What `forcePropagationFloat` propagates

`forcePropagationFloat` is `propagateFloat` with the interval `stlInterval(0,inf)`, which denotes
every time `t ≥ 0`: every observation is final.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer

## Hypotheses
* none

## Conclusion
* it propagates over all times from zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.forcePropagationFloat_spec (eps : 𝕋)
    (obj : OnlineReachSetAnalyzer 𝕋 S d) : -- --- CONCL ---
    obj.forcePropagationFloat eps = obj.propagateFloat eps
        (STLInterval.stlInterval (0 : 𝕋) ⊤ true true toReal_zero_eq.ge) ∧
      (STLInterval.stlInterval (0 : 𝕋) ⊤ true true toReal_zero_eq.ge).set =
        Set.Ici 0 := by -- --- PROOF ---
  refine ⟨rfl, ?_⟩
  rw [STLInterval.set_stlInterval, toReal_zero_eq]
  ext t
  simp only [STLInterval.rawSet, Set.mem_setOf_eq, Set.mem_Ici, STLInterval.toEReal_top]
  constructor
  · rintro ⟨h | ⟨-, h⟩, -⟩
    · exact_mod_cast h.le
    · exact_mod_cast h.le
  · intro h
    refine ⟨?_, Or.inl (EReal.coe_lt_top t)⟩
    rcases h.lt_or_eq with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr ⟨trivial, by rw [← h]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
