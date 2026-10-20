module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioAt

@[expose] public section

/-!
# `Interval.boundaryRatioAt` brackets the coordinate's ratio

A coordinate with a ratio has a certified sign: for a positive direction its bounds bracket `(sup
- start) / dir`, for a negative one `(start - inf) / (-dir)`, the quotients of the exact reading
of the stored floats.

## Inputs
* `I` – interval box
* `dir` – ray direction
* `start` – ray start point
* `i` – coordinate index

## Hypotheses
* none

## Conclusion
* every returned ratio brackets the exact ratio of coordinate `i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boundaryRatioAt_mem {I : Interval (Vec 𝕋 n)} {dir start : Vec 𝕋 n}
    {i : Fin n} : -- --- CONCL ---
    ∀ x ∈ Interval.boundaryRatioAt I dir start i,
      (0 < toReal (dir i) ∧
          toReal x.inf ≤ (toReal (I.sup i) - toReal (start i)) / toReal (dir i) ∧
          (toReal (I.sup i) - toReal (start i)) / toReal (dir i) ≤ toReal x.sup) ∨
        (toReal (dir i) < 0 ∧
          toReal x.inf ≤ (toReal (start i) - toReal (I.inf i)) / -toReal (dir i) ∧
          (toReal
              (start i) - toReal (I.inf i)) / -toReal (dir i) ≤ toReal x.sup) := by -- --- PROOF ---
  intro x (hx : Interval.boundaryRatioAt I dir start i = some x)
  unfold Interval.boundaryRatioAt at hx
  split_ifs at hx with h1 h2
  · -- positive direction
    cases Option.some.inj hx
    have hd : 0 < toReal (dir i) := by simpa [toReal_zero] using toReal_lt_of_ltStrict h1
    left
    refine ⟨hd, le_trans (divDown_le_div _ _ hd) ?_, le_trans ?_ (div_le_divUp _ _ hd)⟩
    · exact div_le_div_of_nonneg_right (subDown_le_sub _ _) hd.le
    · exact div_le_div_of_nonneg_right (sub_le_subUp _ _) hd.le
  · -- negative direction
    cases Option.some.inj hx
    have hd : toReal (dir i) < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict h2
    have hnd : 0 < toReal (neg (dir i)) := by rw [toReal_neg]; linarith
    right
    refine ⟨hd, ?_, ?_⟩
    · have := le_trans (divDown_le_div (subDown (start i) (I.inf i)) (neg (dir i)) hnd)
        (div_le_div_of_nonneg_right (subDown_le_sub (start i) (I.inf i)) hnd.le)
      rwa [toReal_neg] at this
    · have := le_trans (div_le_div_of_nonneg_right (sub_le_subUp (start i) (I.inf i)) hnd.le)
        (div_le_divUp _ _ hnd)
      rwa [toReal_neg] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
