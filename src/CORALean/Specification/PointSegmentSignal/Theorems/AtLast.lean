module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# A signal is constant after its last point

After its last time point a signal keeps the value of the interval stored for it.

## Inputs
* `T` – time type
* `tp` – time points
* `val` – stored values
* `t` – time

## Hypotheses
* `hlen` – two values per time point
* `hne` – there are time points
* `ht` – the time is after all points

## Conclusion
* the value is the last stored interval value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_last {T : Type} [LinearOrder T] (tp : List T) (val : List Bool)
    (hlen : val.length = 2 * tp.length) (hne : tp ≠ []) (t : T)
    (ht : ∀ x ∈ tp, x < t) : -- --- CONCL ---
    (PointSegmentSignal.mk tp val).at t = val.getD (val.length - 1) false := by -- --- PROOF ---
  have h : tp.takeWhile (· ≤ t) = tp := by
    rw [List.takeWhile_eq_self_iff]
    intro x hx; simpa using (ht x hx).le
  have hpos : 0 < tp.length := List.length_pos_iff.mpr hne
  simp only [TimeOrder.exists_mem_eqv_iff, PointSegmentSignal.at, h]
  have hl : tp[tp.length - 1]? = some (tp.getLast hne) := by
    rw [List.getLast_eq_getElem]
    simp [List.getElem?_eq_getElem (by omega : tp.length - 1 < tp.length)]
  rw [hl, if_neg (by have := ht _ (List.getLast_mem hne); simpa using this.ne)]
  congr 1; omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
