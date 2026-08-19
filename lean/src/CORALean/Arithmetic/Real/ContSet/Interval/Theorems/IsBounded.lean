import CORALean.Arithmetic.Real.ContSet.Interval.Interval

/-!
# An interval is bounded

Each coordinate is pinned between two reals, so the box never escapes them. What
an integrand valued in a set needs, and the empty case is covered for free —
`sup i < inf i` denotes `∅`, which is bounded.

The witness is a sum rather than a supremum: each coordinate's own bound is one
term of it, and the rest are non-negative.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n : ℕ}

theorem Interval.isBounded_construct (I : Interval n) : Bornology.IsBounded I.construct := by
  refine isBounded_iff_forall_norm_le.mpr
    ⟨∑ i, (|I.inf i| + |I.sup i|), fun x hx => ?_⟩
  refine (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => by positivity)).mpr fun i => ?_
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => |I.inf i| + |I.sup i|) (fun j _ => by positivity) (Finset.mem_univ i))
  have h := hx i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (I.inf i), abs_nonneg (I.sup i)]
  · linarith [le_abs_self (I.sup i), abs_nonneg (I.inf i)]

end CORALean.Arithmetic.Real
