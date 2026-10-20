module

public import CORALean.ContSet.Interval.Real.Operations.BoundaryPoint
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `Interval.boundaryPoint` is the exit point of the ray

For a start point in the box and a non-zero direction, `boundaryRatio` is the greatest `s` with
`s • dir + startPoint` in the box, so `boundaryPoint` lies in `I` and every point beyond it on
the ray is outside: the boundary point CORA's docstring promises. Per coordinate with `dir i ≠ 0`
the constraint is `s ≤ bound i / dir i`, the ratio is the least of them, and the ones with
`dir i = 0` never bind, the start point being in the box.

## Inputs
* `I` – interval box
* `dir` – ray direction
* `start` – ray start point

## Hypotheses
* `hdir` – direction nonzero
* `hs` – `start` lies in the box

## Conclusion
* the ratio is the greatest parameter keeping the ray inside the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boundaryRatio_isGreatest (I : Interval (Vec ℝ n)) (dir start : Vec ℝ n)
    (hdir : ∃ i, dir i ≠ 0) (hs : start ∈ I.construct) : -- --- CONCL ---
    IsGreatest {s : ℝ | s • dir + start ∈ I.construct}
      (I.boundaryRatio dir start hdir) := by -- --- PROOF ---
  have hs' : ∀ i, I.inf i ≤ start i ∧ start i ≤ I.sup i := fun i => hs i
  -- the face the direction points to: `inf + d * max(sign, 0)` is `sup` or `inf`
  have hB : ∀ i, (I.inf i - start i) + 2 * Interval.radius I i * (if 0 < dir i then (1 : ℝ) else 0)
      = if 0 < dir i then I.sup i - start i else I.inf i - start i := by
    intro i
    split_ifs <;> simp [Interval.radius]
  unfold Interval.boundaryRatio
  simp only [hB]
  -- each bound over `dir i` is non-negative, so the ratio is
  have hnn : ∀ i, dir i ≠ 0 →
      0 ≤ (if 0 < dir i then I.sup i - start i else I.inf i - start i) / dir i := by
    intro i hi
    split_ifs with h
    · exact div_nonneg (sub_nonneg.mpr (hs' i).2) h.le
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr (hs' i).1) (lt_of_le_of_ne (not_lt.mp h) hi).le
  -- the ratio is the least of the per-coordinate bounds
  generalize hRdef : (Finset.univ.filter fun i => dir i ≠ 0).inf'
    (by obtain ⟨i, hi⟩ := hdir; exact ⟨i, by simpa using hi⟩)
    (fun i => (if 0 < dir i then I.sup i - start i else I.inf i - start i) / dir i) = R
  have hle : ∀ i, dir i ≠ 0 →
      R ≤ (if 0 < dir i then I.sup i - start i else I.inf i - start i) / dir i := fun i hi =>
    hRdef ▸ Finset.inf'_le _ (by simpa using hi)
  have hge : ∀ t, (∀ i, dir i ≠ 0 →
      t ≤ (if 0 < dir i then I.sup i - start i else I.inf i - start i) / dir i) → t ≤ R :=
    fun t h => hRdef ▸ Finset.le_inf' _ _ fun i hi => h i (by simpa using hi)
  have hR0 : 0 ≤ R := hge 0 hnn
  constructor
  · -- the point of the ray at the ratio stays in the box
    intro i
    show I.inf i ≤ R * dir i + start i ∧ R * dir i + start i ≤ I.sup i
    rcases lt_trichotomy (dir i) 0 with h | h | h
    · have := hle i h.ne
      rw [if_neg (not_lt.mpr h.le), le_div_iff_of_neg h] at this
      exact ⟨by linarith, by nlinarith [(hs' i).2]⟩
    · rw [h]; simpa using hs' i
    · have := hle i h.ne'
      rw [if_pos h, le_div_iff₀ h] at this
      exact ⟨by nlinarith [(hs' i).1], by linarith⟩
  · -- any point of the ray in the box is no farther: each coordinate bounds `s`
    intro t ht
    refine hge t fun i hi => ?_
    have hti : I.inf i ≤ t * dir i + start i ∧ t * dir i + start i ≤ I.sup i := ht i
    rcases lt_or_gt_of_ne hi with h | h
    · rw [if_neg (not_lt.mpr h.le), le_div_iff_of_neg h]
      linarith [hti.1]
    · rw [if_pos h, le_div_iff₀ h]
      linarith [hti.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
