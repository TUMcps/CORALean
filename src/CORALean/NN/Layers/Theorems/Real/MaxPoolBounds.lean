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
    (hg : ∀ l, l ≠ p → hi (t l) - lo (t p) ≤ g) :
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
