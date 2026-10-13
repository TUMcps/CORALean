module

public import CORALean.NN.Layers.Definitions.SShape
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# An S-shaped derivative rises to `0` and falls after it

An even derivative that does not increase away from `0` does not decrease up to `0`: left of
`0` it is its own mirror image. Which is the shape [1, Thm. 3.2] needs, `f'' ≥ 0` left of the
inflection point and `f'' ≤ 0` right of it, at the inflection point `0`.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SShape.unimodal {df : α → α} (h : SShape df) :
    MonotoneOn df (Set.Iic 0) ∧ AntitoneOn df (Set.Ici 0) := by -- --- PROOF ---
  refine ⟨fun s hs t ht hst => ?_, fun s hs t ht hst => h.anti hs hst⟩
  -- the mirror image of `0 ≤ -t ≤ -s`
  have h1 : (0 : α) ≤ -t := neg_nonneg.mpr ht
  have h2 : -t ≤ -s := neg_le_neg hst
  rw [← h.even s, ← h.even t]
  exact h.anti h1 h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
