module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Appending a point changes nothing before it

Appending a time point `N` above all earlier ones, with its point value `pv` and interval value
`iv`, leaves the signal unchanged below `N`, has value `pv` at `N` and `iv` above it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_snoc_lt {T : Type} [LinearOrder T] (tp : List T) (val : List Bool)
    (N : T) (pv iv : Bool) (hlen : val.length = 2 * tp.length) (hne : tp ≠ []) (t : T)
    (ht : t < N) : -- --- CONCL ---
    (PointSegmentSignal.mk (tp ++ [N]) (val ++ [pv, iv])).at t =
      (PointSegmentSignal.mk tp val).at t := by -- --- PROOF ---
  have hpos : 0 < tp.length := List.length_pos_iff.mpr hne
  have hL : (tp.takeWhile (· ≤ t)).length ≤ tp.length := (List.takeWhile_sublist _).length_le
  have h : ((tp ++ [N]).takeWhile (· ≤ t)).length = (tp.takeWhile (· ≤ t)).length := by
    rw [List.takeWhile_append]
    split_ifs with h1
    · simp [not_le.mpr ht, h1]
    · rfl
  have hi : (tp.takeWhile (· ≤ t)).length - 1 < tp.length := by omega
  simp only [PointSegmentSignal.at, h]
  rw [List.getElem?_append_left hi, List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
