module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Appending a point sets its point value

Appending a time point `N` above all earlier ones, with its point value `pv` and interval value
`iv`, leaves the signal unchanged below `N`, has value `pv` at `N` and `iv` above it.

## Inputs
* `T` – time type
* `tp` – time points
* `val` – stored values
* `N` – appended time point
* `pv` – point value of the new point
* `iv` – interval value after the new point

## Hypotheses
* `hlen` – two values per time point
* `hlt` – the new point is after all earlier points

## Conclusion
* the value at the new point is its point value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_snoc_eq {T : Type} [LinearOrder T] (tp : List T) (val : List Bool)
    (N : T) (pv iv : Bool) (hlen : val.length = 2 * tp.length)
    (hlt : ∀ x ∈ tp, x < N) : -- --- CONCL ---
    (PointSegmentSignal.mk (tp ++ [N]) (val ++ [pv, iv])).at N = pv := by -- --- PROOF ---
  have h : (tp ++ [N]).takeWhile (· ≤ N) = tp ++ [N] := by
    rw [List.takeWhile_eq_self_iff]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simpa using (hlt x hx).le
    · simp at hx; simp [hx]
  simp only [TimeOrder.exists_mem_eqv_iff, PointSegmentSignal.at, h, List.length_append,
    List.length_singleton, Nat.add_sub_cancel]
  have : (tp ++ [N])[tp.length]? = some N := by simp
  rw [this, if_pos rfl, List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
