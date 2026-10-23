module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Appending a point sets the value after it

Appending a time point `N` above all earlier ones, with its point value `pv` and interval value
`iv`, leaves the signal unchanged below `N`, has value `pv` at `N` and `iv` above it.

## Inputs
* `T` – time type
* `tp` – time points
* `val` – stored values
* `N` – appended time point
* `pv` – point value of the new point
* `iv` – interval value after the new point
* `t` – time

## Hypotheses
* `hlen` – two values per time point
* `hlt` – the new point is after all earlier points
* `ht` – the time is after the new point

## Conclusion
* the value after the new point is its interval value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_snoc_gt {T : Type} [LinearOrder T] (tp : List T) (val : List Bool)
    (N : T) (pv iv : Bool) (hlen : val.length = 2 * tp.length) (hlt : ∀ x ∈ tp, x < N) (t : T)
    (ht : N < t) : -- --- CONCL ---
    (PointSegmentSignal.mk (tp ++ [N]) (val ++ [pv, iv])).at t = iv := by -- --- PROOF ---
  have h : (tp ++ [N]).takeWhile (· ≤ t) = tp ++ [N] := by
    rw [List.takeWhile_eq_self_iff]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simpa using ((hlt x hx).trans ht).le
    · simp at hx; simp [hx, ht.le]
  simp only [TimeOrder.exists_mem_eqv_iff, PointSegmentSignal.at, h, List.length_append,
    List.length_singleton, Nat.add_sub_cancel]
  have : (tp ++ [N])[tp.length]? = some N := by simp
  rw [this, if_neg (by simpa using ht.ne), List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
