import CORALean.Arithmetic.Real.ContSet.Zonotope.Zonotope

/-!
# A zonotope is bounded

Coefficients run over `[-1,1]`, so a coordinate reaches at most its centre plus
the row sum of absolute generator entries — the same quantity `radius` computes,
here only as a bound and never stored.

The witness is a sum over coordinates rather than a supremum: each coordinate's
own bound is one term of it, and the rest are non-negative.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n : ℕ}

theorem Zonotope.isBounded_construct (Z : Zonotope n) : Bornology.IsBounded Z.construct := by
  refine isBounded_iff_forall_norm_le.mpr
    ⟨∑ i, (|Z.c i| + ∑ j, |Z.G i j|), ?_⟩
  rintro x ⟨β, hβ, hx⟩
  refine (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => by positivity)).mpr fun i => ?_
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => |Z.c i| + ∑ j, |Z.G i j|) (fun j _ => by positivity) (Finset.mem_univ i))
  rw [Real.norm_eq_abs, hx i]
  refine le_trans (abs_add_le _ _) (add_le_add (le_refl _) ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)

end CORALean.Arithmetic.Real
