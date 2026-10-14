module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The negative of an STL interval

`-{t | …}` swaps the two ends: `rawSet l u lc rc` negated is `rawSet (-u) (-l) rc lc`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- Negating `rawSet l u lc rc` gives `rawSet (-u) (-l) rc lc`. -/
theorem STLInterval.rawSet_neg (l u : EReal) (lc rc : Bool) :
    -(rawSet l u lc rc) = rawSet (-u) (-l) rc lc := by -- --- PROOF ---
  ext t
  show -t ∈ rawSet l u lc rc ↔ _
  simp only [rawSet, Set.mem_setOf_eq, EReal.coe_neg]
  rw [and_comm]
  have key : ∀ a b : EReal, a = -b ↔ -a = b :=
    fun a b => ⟨fun h => by rw [h, neg_neg], fun h => by rw [← h, neg_neg]⟩
  simp [EReal.lt_neg_comm, EReal.neg_lt_comm, eq_comm, key]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
