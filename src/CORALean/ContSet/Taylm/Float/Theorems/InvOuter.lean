module

public import CORALean.ContSet.Taylm.Float.Operations.Inv
public import CORALean.ContSet.Taylm.Float.Theorems.InvCoefMem
public import CORALean.ContSet.Taylm.Float.Theorems.InvBoundGe
public import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter

@[expose] public section

/-!
# `Taylm.inv` encloses `1 / f`, over a floating-point scalar

Where the hull of the centre and the range stays at a positive distance `m` from zero, `x ↦ 1/x`
is smooth on it, its Taylor coefficients at the centre lie in the rounded interval `invCoef`
(`invCoef_mem`), and its `(N+1)`-th derivative is below the rounded `invBound` (`invBound_ge`).
`Taylm.taylor_outer` does the rest. Outer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.inv_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hm : 0 < toReal (maximum (minimum T.constCoef T.bounds.inf)
      (neg (maximum T.constCoef T.bounds.sup)))) :
    T.inv.Encloses fun t => (f t)⁻¹ := by -- --- PROOF ---
  rw [toReal_maximum, toReal_minimum, toReal_neg, toReal_maximum] at hm
  -- every point of the hull is at least `m` away from zero
  have hξ : ∀ ξ ∈ Set.Icc (min (toReal T.constCoef) (toReal T.bounds.inf))
      (max (toReal T.constCoef) (toReal T.bounds.sup)),
      max (min (toReal T.constCoef) (toReal T.bounds.inf))
        (-max (toReal T.constCoef) (toReal T.bounds.sup)) ≤ |ξ| ∧ ξ ≠ 0 := by
    intro ξ hξ
    rcases lt_max_iff.mp hm with hpos | hneg
    · have h0 : 0 < ξ := lt_of_lt_of_le hpos hξ.1
      have hM : max (min (toReal T.constCoef) (toReal T.bounds.inf))
          (-max (toReal T.constCoef) (toReal T.bounds.sup)) =
          min (toReal T.constCoef) (toReal T.bounds.inf) :=
        max_eq_left (by linarith [hξ.1, hξ.2])
      rw [hM, abs_of_pos h0]
      exact ⟨hξ.1, ne_of_gt h0⟩
    -- the negative side: the hull lies below zero
    · have h0 : ξ < 0 := by linarith [hξ.2]
      have hM : max (min (toReal T.constCoef) (toReal T.bounds.inf))
          (-max (toReal T.constCoef) (toReal T.bounds.sup)) =
          -max (toReal T.constCoef) (toReal T.bounds.sup) :=
        max_eq_right (by linarith [hξ.1, hξ.2])
      rw [hM, abs_of_neg h0]
      exact ⟨by linarith [hξ.2], ne_of_lt h0⟩
  -- the centre is itself in the hull, so not zero
  have hc0 : toReal T.constCoef ≠ 0 :=
    (hξ _ ⟨min_le_left _ _, le_max_left _ _⟩).2
  refine Taylm.taylor_outer h Inv.inv T.constCoef _ _ _ _
    (fun k _ => Taylm.invCoef_mem T.constCoef hc0 k)
    (fun ξ hx => contDiffAt_inv ℝ (hξ ξ hx).2) (fun ξ hx => ?_) le_rfl
  refine Taylm.invBound_ge _ ?_ _ ?_
  · rw [toReal_maximum, toReal_minimum, toReal_neg, toReal_maximum]; exact hm
  · rw [toReal_maximum, toReal_minimum, toReal_neg, toReal_maximum]; exact (hξ ξ hx).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
