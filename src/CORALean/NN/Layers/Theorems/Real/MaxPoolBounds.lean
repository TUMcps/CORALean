module

public import CORALean.Global.Tensor
public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# How far a window's maximum rises above its pivot

At least nothing, and at most any `g` bounding what the other taps reach above the pivot's
lower bound. `g` is arbitrary, which is what lets a layer round its gap up in any precision and
reuse this unchanged.

## Inputs
* `k` – window size minus one
* `t` – input index of every window position
* `p` – pivot position
* `lo` – lower bounds of the inputs
* `hi` – upper bounds of the inputs
* `x` – input point
* `g` – bound on the other taps' reach

## Hypotheses
* `hx` – the point lies in the bounds
* `hg0` – the reach bound is nonnegative
* `hg` – every other tap reaches at most the bound above the pivot

## Conclusion
* the window's maximum exceeds the pivot by between zero and the bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The window's maximum above its pivot, for *any* `g` bounding the other taps' reach. -/
theorem maxPool_bounds {k : ℕ} (t : Fin (k + 1) → Fin n) (p : Fin (k + 1))
    (lo hi x : Vec ℝ n) (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) {g : ℝ} (hg0 : 0 ≤ g)
    (hg : ∀ l, l ≠ p → hi (t l) - lo (t p) ≤ g) : -- --- CONCL ---
    0 ≤ windowMax (fun l => x (t l)) - x (t p) ∧
      windowMax (fun l => x (t l)) - x (t p) ≤ g := by -- --- PROOF ---
  refine ⟨by linarith [le_windowMax (fun l => x (t l)) p], ?_⟩
  have h : windowMax (fun l => x (t l)) ≤ x (t p) + g := by
    refine windowMax_le fun l => ?_
    by_cases hl : l = p
    · rw [hl]
      linarith
    · linarith [(hx (t l)).2, (hx (t p)).1, hg l hl]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
