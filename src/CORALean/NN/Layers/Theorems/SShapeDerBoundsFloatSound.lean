module

public import CORALean.NN.Layers.Operations.SShapeDerBoundsFloat
public import CORALean.NN.Layers.Definitions.SShape

@[expose] public section

/-!
# The float derivative bounds hold

For an S-shaped real derivative `df` that `dfLo` and `dfHi` bound at every stored point, `df t`
lies in `sShapeDerBoundsFloat dfLo dfHi l u` for every real `t` between the real values of `l`
and `u`. An outer statement: it holds in the cases the comparison does not decide too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `df t` lies in the float bounds for every `t` in `[l, u]`. -/
theorem sShapeDerBoundsFloat_sound {df : ℝ → ℝ} (h : SShape df) {dfLo dfHi : 𝕋 → 𝕋}
    (hlo : ∀ a, toReal (dfLo a) ≤ df (toReal a)) (hhi : ∀ a, df (toReal a) ≤ toReal (dfHi a))
    {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (sShapeDerBoundsFloat dfLo dfHi l u).inf ≤ df t ∧
      df t ≤ toReal (sShapeDerBoundsFloat dfLo dfHi l u).sup := by -- --- PROOF ---
  -- `df` rises towards `0` on the left, by evenness
  have hneg : ∀ {s t : ℝ}, s ≤ t → t ≤ 0 → df s ≤ df t := fun {s t} hst ht => by
    rw [← h.even s, ← h.even t]
    exact h.anti (neg_nonneg.mpr ht) (neg_le_neg hst)
  -- the peak is at `0`
  have hpeak : df t ≤ df 0 := by
    rcases le_total 0 t with ht | ht
    · exact h.anti le_rfl ht
    · exact hneg ht le_rfl
  unfold sShapeDerBoundsFloat
  refine ⟨?_, ?_⟩
  · -- the least value is at one of the ends
    rw [toReal_minimum]
    rcases le_total 0 t with ht | ht
    · exact le_trans (min_le_right _ _) (le_trans (hlo u) (h.anti ht hu))
    · exact le_trans (min_le_left _ _) (le_trans (hlo l) (hneg hl ht))
  · -- the greatest value, by the case the certified comparisons name
    dsimp only
    by_cases h1 : (le l zero && le zero u) = true
    · rw [if_pos h1]
      have := hhi zero
      rw [toReal_zero] at this
      exact le_trans hpeak this
    · rw [if_neg h1]
      -- right of `0`: `df` decreases from `l` on
      by_cases h2 : le zero l = true
      · rw [if_pos h2]
        have h0 := toReal_le_of_le h2
        rw [toReal_zero] at h0
        exact le_trans (h.anti h0 hl) (hhi l)
      · rw [if_neg h2]
        -- left of `0`: `df` increases up to `u`
        by_cases h3 : le u zero = true
        · rw [if_pos h3]
          have h0 := toReal_le_of_le h3
          rw [toReal_zero] at h0
          exact le_trans (hneg hu h0) (hhi u)
        · rw [if_neg h3]
          -- undecided: the peak bounds `df` everywhere
          have := hhi zero
          rw [toReal_zero] at this
          exact le_trans hpeak this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
