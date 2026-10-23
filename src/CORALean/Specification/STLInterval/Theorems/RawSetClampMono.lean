module

public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.RawSetMono

@[expose] public section

/-!
# Cutting at zero after moving the bounds outward

The cut of `minus` and `minkDiff`, applied to outward bounds `l' ≤ l` and `u ≤ u'`, keeps the times
`≥ 0` of the exact interval: a lower bound that only the outward one takes below `0` is replaced
by the closed `0`, still below the exact one.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `l'` – lowered lower bound
* `u'` – raised upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `hl` – the new lower bound is at most the old
* `hu` – the new upper bound is at least the old

## Conclusion
* the exact times `≥ 0` are among those of the cut outward interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.rawSet_clamp_mono {l u l' u' : EReal} {lc rc : Bool} (hl : l' ≤ l)
    (hu : u ≤ u') : -- --- CONCL ---
    rawSet l u lc rc ∩ Set.Ici 0 ⊆
      if l' < 0 then rawSet 0 u' true rc else rawSet l' u' lc rc := by -- --- PROOF ---
  rw [rawSet_clamp]
  by_cases h : l < 0
  · -- both are cut to the closed `0`
    rw [if_pos h, if_pos (hl.trans_lt h)]
    exact rawSet_mono le_rfl hu
  · rw [if_neg h]
    by_cases h' : l' < 0
    · -- only the outward bound is cut: the closed `0` is still below `l`
      rw [if_pos h']
      rintro t ⟨h1, h2⟩
      refine ⟨?_, (rawSet_mono le_rfl hu ⟨h1, h2⟩).2⟩
      rcases (not_lt.1 h).lt_or_eq with h0 | h0
      · rcases h1 with h1 | ⟨-, h1⟩
        · exact Or.inl (h0.trans h1)
        · exact Or.inl (h1 ▸ h0)
      · rcases h1 with h1 | ⟨-, h1⟩
        · exact Or.inl (h0 ▸ h1)
        · exact Or.inr ⟨rfl, h0.trans h1⟩
    · rw [if_neg h']
      exact rawSet_mono hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
