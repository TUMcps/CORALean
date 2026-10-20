module

public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.empty` denotes `∅`

The crossed remainder is unsatisfiable, so no point is in the range set. `0 < n`, as for
`Interval.empty`: with no coordinate there is no remainder to cross.

## Inputs
* none

## Hypotheses
* `hn` – the dimension is positive

## Conclusion
* the empty model family denotes the empty set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.empty_exact (hn : 0 < n) : -- --- CONCL ---
    Taylm.construct (Taylm.empty n) = ∅ := by -- --- PROOF ---
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨t, _, h⟩ := hx
  have := h ⟨0, hn⟩
  simp [Taylm.empty, Taylm.poly] at this
  exact absurd (this.1.trans this.2) (by norm_num)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
