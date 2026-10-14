module

public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `Interval.mtimes` never returns crossed bounds

Termwise `min ≤ max`, whichever matrix and whichever interval: the argument may
itself have crossed bounds and the result still has bounds in order, so there is
no hypothesis to carry.

That is what lets a computed image box be handed straight to a layer that
commits to its centre — `Layer.linearWithError` asks exactly this of the error
box a neuron merge builds as `W(·,B) · Y(B)`. The fact is about `mtimes` and
mentions no network, so it lives here rather than beside that layer.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimes_isNonempty (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) :
    (Interval.mtimes M I).IsNonempty := fun i => by
  show (∑ k, min (M i k * I.inf k) (M i k * I.sup k))
      ≤ ∑ k, max (M i k * I.inf k) (M i k * I.sup k)
  exact Finset.sum_le_sum fun k _ => min_le_max

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
