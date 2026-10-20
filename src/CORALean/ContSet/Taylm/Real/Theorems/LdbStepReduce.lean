module

public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import CORALean.ContSet.Taylm.Real.Operations.LdbStep
public import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfEqLinAddHigher
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# What LDB cuts off is above `Min`

[1, Sec. 2], step (3)(a): a point outside the kept part lies more than `d/|Lᵢ|` from the left end
in some direction `i`, so the linear part alone puts it more than `d` above `M`, that is above
`Min`, which some point stays below.

## Inputs
* `T` – Taylor model
* `g` – enclosed function
* `s` – point

## Hypotheses
* `h` – the model encloses the function
* `hs` – point lies in the unit box
* `hR` – point is cut off by the step

## Conclusion
* the function's value exceeds the step's upper bound

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldbStep_reduce {T : Taylm n} {g : Vec ℝ n → ℝ} (h : T.Encloses g) {s : Vec ℝ n}
    (hs : s ∈ Taylm.box n) (hR : ¬ Taylm.InBox T.ldbStep.2 s) :
    T.ldbStep.1.sup < g s := by -- --- PROOF ---
  have hr := h s hs
  have hdec := Taylm.polyOf_eq_lin_add_higher T.terms s
  have hb := Taylm.polyBounds_mem (Taylm.higherTerms T.terms) hs
  -- the linear part exceeds its least value by at least one coordinate's share
  have hlin : ∀ k, -∑ j, |Taylm.linCoef T.terms j|
      + (Taylm.linCoef T.terms k * s k + |Taylm.linCoef T.terms k|)
      ≤ ∑ j, Taylm.linCoef T.terms j * s j := by
    intro k
    have hpos : ∀ j, 0 ≤ Taylm.linCoef T.terms j * s j + |Taylm.linCoef T.terms j| := by
      intro j
      have := abs_le.1 (hs j)
      have h1 := neg_abs_le (Taylm.linCoef T.terms j * s j)
      rw [abs_mul] at h1
      nlinarith [abs_nonneg (Taylm.linCoef T.terms j), abs_nonneg (s j), abs_le.2 this]
    have := Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ k)
    rw [Finset.sum_add_distrib] at this
    linarith
  -- a direction in which the point is outside the kept part
  simp only [Taylm.InBox, not_forall] at hR
  obtain ⟨k, hk⟩ := hR
  have hsk := abs_le.1 (hs k)
  have hlk := hlin k
  simp only [Taylm.ldbStep] at hk ⊢
  simp only [Taylm.poly] at hr
  set L := Taylm.linCoef T.terms
  set Min := min
    (T.constCoef + ∑ k, |L k| + ((Taylm.polyBounds (Taylm.higherTerms T.terms)).sup + T.rem.sup))
    (min ((T.poly fun k => if 0 < L k then -1 else 1) + T.rem.sup) (T.poly 0 + T.rem.sup))
  set M := T.constCoef - ∑ k, |L k| + ((Taylm.polyBounds (Taylm.higherTerms T.terms)).inf +
      T.rem.inf)
  -- `g s` is at least `M` plus the share of coordinate `k`
  have hgs : M + (L k * s k + |L k|) ≤ g s := by
    simp only [M, Taylm.constCoef]
    linarith [hr.1, hb.1]
  -- the coordinate outside its kept part, by the sign of its slope
  split_ifs at hk with h1 h2
  · have hk' : -1 + (Min - M) / L k < s k := by
      by_contra hc; push Not at hc; exact hk ⟨hsk.1, hc⟩
    rw [abs_of_pos h1.1] at hgs
    have : Min - M < L k * (s k + 1) := by
      have := (div_lt_iff₀ h1.1).1 (by linarith : (Min - M) / L k < s k + 1)
      linarith
    linarith
  · have hneg : L k < 0 := h2.1
    have hk' : s k < 1 - (Min - M) / -L k := by
      by_contra hc; push Not at hc; exact hk ⟨hc, hsk.2⟩
    rw [abs_of_neg hneg] at hgs
    have : Min - M < -L k * (1 - s k) := by
      have := (div_lt_iff₀ (by linarith : (0:ℝ) < -L k)).1
        (by linarith : (Min - M) / -L k < 1 - s k)
      linarith
    linarith
  · exact absurd ⟨hsk.1, hsk.2⟩ hk

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
