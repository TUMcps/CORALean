module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Cancelling redundant reachable sets

[1, Sec. VI-B]: after splits, the number of reachable sets grows with every step. A segment
of the current interval is dropped when its polytope enclosure has an empty set difference with
the polytopes of the segments of the past `ζ` time steps, and only every `δ`-th step, the
check being expensive. A segment is `β`, `poly` the polytope enclosing it (a conversion the
caller supplies), `hist` the steps' segment lists, newest first. The paper then converts the
kept polytopes back to zonotopes; that conversion is left to the caller.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {β : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- [1, Sec. VI-B]: at step `k`, with `δ ∣ k`, drop each segment whose polytope minus the
polytopes of the past `ζ` steps is empty. -/
noncomputable def NonlinearSys.cancelRedundant (poly : β → Set (Vec ℝ n)) (δ ζ k : ℕ)
    (hist : List (List β)) (segs : List β) : List β :=
  if δ ∣ k then
    segs.filter fun s =>
      if (poly s \ ⋃ t ∈ hist.take ζ, ⋃ s' ∈ t, poly s') = ∅ then false else true
  else segs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
