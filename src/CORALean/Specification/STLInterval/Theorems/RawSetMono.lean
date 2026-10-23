module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# Moving the bounds outward keeps the times

Lowering the lower bound and raising the upper one, the flags kept, gives a `rawSet` that holds
every time of the first: what an outward rounding of the bounds does.

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
* the old times are among the new ones
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.rawSet_mono {l u l' u' : EReal} {lc rc : Bool} (hl : l' ≤ l)
    (hu : u ≤ u') : -- --- CONCL ---
    rawSet l u lc rc ⊆ rawSet l' u' lc rc := by -- --- PROOF ---
  rintro t ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  -- the lower test passes against the lower bound, the upper one against the higher
  · rcases hl.lt_or_eq with hl | rfl
    · rcases h1 with h1 | ⟨-, h1⟩
      · exact Or.inl (hl.trans h1)
      · exact Or.inl (h1 ▸ hl)
    · exact h1
  · rcases hu.lt_or_eq with hu | rfl
    · rcases h2 with h2 | ⟨-, h2⟩
      · exact Or.inl (h2.trans hu)
      · exact Or.inl (h2 ▸ hu)
    · exact h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
