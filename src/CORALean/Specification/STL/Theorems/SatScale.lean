module

public import CORALean.Specification.STL.Operations.FormulaScale

@[expose] public section

/-!
# A scaled formula on a trace is the formula on the scaled trace

`ξ ⊨ₜ φ.scale c ⇔ (t ↦ ξ(tc)) ⊨ₜ φ` for `c > 0`: how a result for `c = 1`, like [1, Table 1], and
[1, Lemma 4]'s `c`-divisible formulas are a result for every step `c`.

## Inputs
* `c` – scaling factor
* `φ` – formula
* `ξ` – trace

## Hypotheses
* `hc` – the factor is positive

## Conclusion
* the scaled formula holds iff the formula holds on the scaled trace

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Shifting the scaled trace by `t` is scaling the trace shifted by `t * c`. -/
theorem STL.Formula.aux_shift_scale (c t : ℝ≥0) (ξ : ℝ≥0 → X) :
    Time.shift (fun s => ξ (s * c)) t = fun s => (Time.shift ξ (t * c)) (s * c) := by
  funext s
  show ξ ((s + t) * c) = ξ (s * c + t * c)
  rw [add_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_scale {c : ℝ≥0} (hc : 0 < c) (φ : STL.Formula X)
    (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (φ.scale c).Sat ξ ↔ φ.Sat (fun t => ξ (t * c)) := by -- --- PROOF ---
  induction φ generalizing ξ with
  | atom p => simp [STL.Formula.scale, STL.Formula.Sat]
  | not φ ih => simp only [STL.Formula.scale, STL.Formula.Sat, ih]
  | or φ ψ ihφ ihψ => simp only [STL.Formula.scale, STL.Formula.Sat, ihφ, ihψ]
  | «until» a b φ ψ ihφ ihψ =>
    simp only [STL.Formula.scale, STL.Formula.Sat, ihφ, ihψ]
    constructor
    · -- the witness `t` of the scaled formula is `t / c` on the scaled trace
      rintro ⟨t, h₁, h₂, h₃, h₄⟩
      have e : t / c * c = t := div_mul_cancel₀ t hc.ne'
      refine ⟨t / c, ?_, ?_, ?_, fun t' ht' => ?_⟩
      · exact (le_div_iff₀ hc).2 h₁
      · exact (div_le_iff₀ hc).2 h₂
      · rw [STL.Formula.aux_shift_scale, e]; exact h₃
      · rw [STL.Formula.aux_shift_scale]
        exact h₄ _ (by rw [← e]; exact mul_lt_mul_of_pos_right ht' hc)
    · -- conversely a witness `t` of the unscaled formula is `t * c` of the scaled one
      rintro ⟨t, h₁, h₂, h₃, h₄⟩
      refine ⟨t * c, ?_, ?_, ?_, fun t' ht' => ?_⟩
      · exact mul_le_mul_of_nonneg_right h₁ hc.le
      · exact mul_le_mul_of_nonneg_right h₂ hc.le
      · rw [STL.Formula.aux_shift_scale] at h₃; exact h₃
      · -- a time below `t * c` is `t'' * c` with `t'' < t`
        have e : t' / c * c = t' := div_mul_cancel₀ t' hc.ne'
        have := h₄ (t' / c) (by
          rw [div_lt_iff₀ hc]; exact ht')
        rw [STL.Formula.aux_shift_scale, e] at this
        exact this
  | finOpen d φ ih =>
    -- a time in the open window `(0, d c)` is `t c` for a time `t` in `(0, d)`
    simp only [STL.Formula.scale, STL.Formula.Sat, ih]
    constructor
    · -- the scaled window's witness divided by `c`
      rintro ⟨t, h₀, h₁, h⟩
      have e : t / c * c = t := div_mul_cancel₀ t hc.ne'
      refine ⟨t / c, div_pos h₀ hc, (div_lt_iff₀ hc).2 h₁, ?_⟩
      rw [STL.Formula.aux_shift_scale, e]; exact h
    · rintro ⟨t, h₀, h₁, h⟩
      refine ⟨t * c, mul_pos h₀ hc, mul_lt_mul_of_pos_right h₁ hc, ?_⟩
      rwa [STL.Formula.aux_shift_scale] at h
  | globOpen d φ ih =>
    -- as for the window `F(0, d c)`, now for every time of it
    simp only [STL.Formula.scale, STL.Formula.Sat, ih]
    constructor
    · intro h t h₀ h₁
      have := h (t * c) (mul_pos h₀ hc) (mul_lt_mul_of_pos_right h₁ hc)
      rwa [← STL.Formula.aux_shift_scale] at this
    · intro h t h₀ h₁
      have e : t / c * c = t := div_mul_cancel₀ t hc.ne'
      have := h (t / c) (div_pos h₀ hc) ((div_lt_iff₀ hc).2 h₁)
      rw [STL.Formula.aux_shift_scale, e] at this
      exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
