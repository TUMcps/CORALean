import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.ActivationPoly

/-!
# A polynomial evaluated outward at a float

What a sample point needs of a fit. `PolyRelaxation.Sound` measures `σ` against
the coefficients *stored*, so an enclosure of `Real.evalPoly` at those floats is
the whole of the fit's rounding, and nothing is left to pad afterwards.

Interval arithmetic rather than Horner, and sign is why. `mul_le_mulUp` bounds a
product in one direction with no hypothesis on either factor, but composing
`mulUp x (mulUp ...)` needs `0 ≤ x`, and no float comparison establishes a sign:
`le` is constrained in one direction only. `mulRangeUp` takes both products and
the larger of them, which asks nothing of the sign at all.

`powRange` carries the two ends together, each end of `t ^ (k + 1)` reading both
ends of `t ^ k`. `one` is exact, so the constant term pays no rounding, and a
coefficient stored exactly is bracketed by two products and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `a * x` from below, for every `x` the bracket `[lo, hi]` holds. -/
def mulRangeDown (a lo hi : 𝕋) : 𝕋 := minimum (mulDown a lo) (mulDown a hi)

/-- And from above, the same two products the other way. -/
def mulRangeUp (a lo hi : 𝕋) : 𝕋 := maximum (mulUp a lo) (mulUp a hi)

theorem mulRangeDown_le {a lo hi : 𝕋} {x : ℝ} (h1 : toReal lo ≤ x) (h2 : x ≤ toReal hi) :
    toReal (mulRangeDown a lo hi) ≤ toReal a * x := by -- --- PROOF ---
  rw [mulRangeDown, toReal_minimum]
  -- multiplication by `a` is monotone one way or the other, so one end bounds it
  rcases le_or_gt 0 (toReal a) with ha | ha
  · exact le_trans (min_le_left _ _)
      (le_trans (mulDown_le_mul a lo) (mul_le_mul_of_nonneg_left h1 ha))
  · exact le_trans (min_le_right _ _)
      (le_trans (mulDown_le_mul a hi) (mul_le_mul_of_nonpos_left h2 ha.le))

theorem le_mulRangeUp {a lo hi : 𝕋} {x : ℝ} (h1 : toReal lo ≤ x) (h2 : x ≤ toReal hi) :
    toReal a * x ≤ toReal (mulRangeUp a lo hi) := by -- --- PROOF ---
  rw [mulRangeUp, toReal_maximum]
  -- the same case split, each end now reached from above
  rcases le_or_gt 0 (toReal a) with ha | ha
  · exact le_trans (le_trans (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mulUp a hi))
      (le_max_right _ _)
  · exact le_trans (le_trans (mul_le_mul_of_nonpos_left h1 ha.le) (mul_le_mulUp a lo))
      (le_max_left _ _)

/-- `t ^ k` bracketed, both ends carried together since each reads both. -/
def powRange (t : 𝕋) : ℕ → 𝕋 × 𝕋
  | 0 => (one, one)
  | k + 1 => (mulRangeDown t (powRange t k).1 (powRange t k).2,
      mulRangeUp t (powRange t k).1 (powRange t k).2)

theorem powRange_bounds (t : 𝕋) (k : ℕ) :
    toReal (powRange t k).1 ≤ toReal t ^ k
      ∧ toReal t ^ k ≤ toReal (powRange t k).2 := by -- --- PROOF ---
  induction k with
  | zero =>
    -- `one` is exact, so the empty product is bracketed by itself
    rw [pow_zero]
    exact ⟨le_of_eq toReal_one, le_of_eq toReal_one.symm⟩
  | succ k ih =>
    have hcomm : toReal t ^ (k + 1) = toReal t * toReal t ^ k := by ring
    refine ⟨?_, ?_⟩
    · show toReal (mulRangeDown t (powRange t k).1 (powRange t k).2) ≤ _
      rw [hcomm]
      exact mulRangeDown_le ih.1 ih.2
    · show _ ≤ toReal (mulRangeUp t (powRange t k).1 (powRange t k).2)
      rw [hcomm]
      exact le_mulRangeUp ih.1 ih.2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial the stored coefficients denote, from below. -/
def evalPolyDown (c : Fin (n + 1) → 𝕋) (t : 𝕋) : 𝕋 :=
  sumDown fun i => mulRangeDown (c i) (powRange t (i : ℕ)).1 (powRange t (i : ℕ)).2

/-- And from above, the same terms rounded the other way. -/
def evalPolyUp (c : Fin (n + 1) → 𝕋) (t : 𝕋) : 𝕋 :=
  sumUp fun i => mulRangeUp (c i) (powRange t (i : ℕ)).1 (powRange t (i : ℕ)).2

theorem evalPolyDown_le (c : Fin (n + 1) → 𝕋) (t : 𝕋) :
    toReal (evalPolyDown c t) ≤ Real.evalPoly (fun k => toReal (c k)) (toReal t) := by
  show toReal (sumDown _) ≤ ∑ i, toReal (c i) * toReal t ^ (i : ℕ)
  refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_)
  exact mulRangeDown_le (powRange_bounds t (i : ℕ)).1 (powRange_bounds t (i : ℕ)).2

theorem le_evalPolyUp (c : Fin (n + 1) → 𝕋) (t : 𝕋) :
    Real.evalPoly (fun k => toReal (c k)) (toReal t) ≤ toReal (evalPolyUp c t) := by
  show (∑ i, toReal (c i) * toReal t ^ (i : ℕ)) ≤ toReal (sumUp _)
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  exact le_mulRangeUp (powRange_bounds t (i : ℕ)).1 (powRange_bounds t (i : ℕ)).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
