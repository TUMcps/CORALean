module

public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Norm

@[expose] public section

/-!
# `Interval.norm` bounds every member

Coordinatewise a member sits between the endpoints, so its magnitude is at most the larger
endpoint magnitude (`aux_abs_le_max_abs`); the Euclidean norm is monotone in magnitudes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.norm_le {I : Interval (Vec ℝ n)} {x : Vec ℝ n} (hx : x ∈ construct I) :
    ‖x‖₂ ≤ I.norm := by -- --- PROOF ---
  unfold Interval.norm norm₂
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
  -- the larger endpoint magnitude dominates `|x i|`, then square both sides
  have hm : |x i| ≤ max |I.inf i| |I.sup i| := by
    refine abs_le.mpr ⟨?_, h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    linarith [(neg_abs_le (I.inf i)).trans h.1, neg_le_neg (le_max_left |I.inf i| |I.sup i|)]
  rw [← sq_abs (x i), ← sq_abs (max _ _), abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
  exact pow_le_pow_left₀ (abs_nonneg _) hm 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
