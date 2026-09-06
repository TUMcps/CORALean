import CORALean.NN.Layers.PolyRelaxation

/-!
# Bounding the fit's derivative, so the sampling bound can be used

`PolyRelaxation.ofSampling` asks for an `M` with `|σ' - p'| ≤ M` on the box and
nothing supplies one, which leaves the whole apparatus unusable at a concrete
activation. This file is the polynomial half of it: `evalPolyDeriv` bracketed
over the box, which against a bracket for `σ'` — what `sigmoidDerivLo` and
`sigmoidDerivHi` already prove — is `M`.

A centre and a radius rather than one absolute bound, because the linear
coefficient is the derivative's constant term and no box widens it. That is what
keeps order 1 exact: the radius is zero there and `polyDerivDiff` is the bracket
`Relaxation.ofDeriv` already works with, so routing an affine relaxation through
the polynomial machinery gives nothing away.

Above the linear term the radius is crude — `|c i| · i · max(|l|,|u|)^(i-1)`
puts every monomial at the worse end of the box and takes every sign against
itself. It owes only soundness, exactly as the fit does: a loose `M` is paid for
in sample spacing, never in correctness.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- What the polynomial's derivative is bracketed around: its linear
coefficient, which at order 1 is the whole derivative. -/
def polyDerivCenter {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), if (i : ℕ) = 1 then c i else 0

/-- How far the remaining monomials move that centre over `[l, u]`. -/
noncomputable def polyDerivRadius {n : ℕ} (c : Fin (n + 1) → ℝ) (l u : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), if (i : ℕ) = 1 then 0
    else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)

/-- The polynomial's derivative over the box, termwise: the linear coefficient
exactly, every other monomial at the end of the box furthest from zero. -/
theorem abs_evalPolyDeriv_sub_center_le {n : ℕ} (c : Fin (n + 1) → ℝ) {l u t : ℝ}
    (hl : l ≤ t) (hu : t ≤ u) :
    |evalPolyDeriv c t - polyDerivCenter c| ≤ polyDerivRadius c l u := by
  have hlm : |l| ≤ max |l| |u| := le_max_left _ _
  have hum : |u| ≤ max |l| |u| := le_max_right _ _
  -- a point of the box is no further from zero than the worse of its ends
  have htR : |t| ≤ max |l| |u| := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le l], by linarith [le_abs_self u]⟩
  have hterm : ∀ i : Fin (n + 1),
      |c i * ((i : ℕ) * t ^ ((i : ℕ) - 1)) - (if (i : ℕ) = 1 then c i else 0)|
        ≤ (if (i : ℕ) = 1 then 0 else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)) := by
    intro i
    by_cases hi : (i : ℕ) = 1
    · -- the linear term is its own coefficient, so the centre absorbs it
      rw [if_pos hi, if_pos hi, hi]
      norm_num
    · have habs : |c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))|
          = |c i| * (i : ℕ) * |t| ^ ((i : ℕ) - 1) := by
        rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
        ring
      rw [if_neg hi, if_neg hi, sub_zero, habs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) htR _)
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hsum : evalPolyDeriv c t - polyDerivCenter c
      = ∑ i : Fin (n + 1),
        (c i * ((i : ℕ) * t ^ ((i : ℕ) - 1)) - (if (i : ℕ) = 1 then c i else 0)) := by
    rw [Finset.sum_sub_distrib]
    rfl
  rw [hsum]
  show _ ≤ ∑ i : Fin (n + 1), if (i : ℕ) = 1 then 0
    else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => hterm i)

/-- The `M` that `ofSampling` asks for, out of a bracket for `σ'` and one for
the fit's derivative: the two subtracted, at the worse end. -/
noncomputable def polyDerivDiff (lo hi ctr rad : ℝ) : ℝ :=
  max |lo - ctr - rad| |hi - ctr + rad|

/-- A bracket for `σ'` over the box bounds what `ofSampling` asks about, since
the fit's own derivative is bracketed by construction. -/
theorem abs_sub_evalPolyDeriv_le {n : ℕ} {c : Fin (n + 1) → ℝ} {σ' : ℝ → ℝ}
    {lo hi l u x : ℝ} (hlo : lo ≤ σ' x) (hhi : σ' x ≤ hi) (hl : l ≤ x) (hu : x ≤ u) :
    |σ' x - evalPolyDeriv c x|
      ≤ polyDerivDiff lo hi (polyDerivCenter c) (polyDerivRadius c l u) := by
  set ctr := polyDerivCenter c
  set rad := polyDerivRadius c l u
  obtain ⟨h₁, h₂⟩ := abs_le.mp (abs_evalPolyDeriv_sub_center_le c hl hu)
  -- each end of the difference is under the `max` the definition takes
  have hL : -|lo - ctr - rad| ≤ lo - ctr - rad := neg_abs_le _
  have hU : hi - ctr + rad ≤ |hi - ctr + rad| := le_abs_self _
  have hlm : |lo - ctr - rad| ≤ max |lo - ctr - rad| |hi - ctr + rad| := le_max_left _ _
  have hum : |hi - ctr + rad| ≤ max |lo - ctr - rad| |hi - ctr + rad| := le_max_right _ _
  show |σ' x - evalPolyDeriv c x| ≤ max |lo - ctr - rad| |hi - ctr + rad|
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- At order 1 the radius vanishes and the centre is the slope, so this is the
bracket `Relaxation.ofDeriv` works with and no precision is lost. -/
theorem polyDerivDiff_one (lo hi : ℝ) (c : Fin 2 → ℝ) (l u : ℝ) :
    polyDerivDiff lo hi (polyDerivCenter c) (polyDerivRadius c l u)
      = max |lo - c 1| |hi - c 1| := by
  have hctr : polyDerivCenter c = c 1 := by
    show (∑ i : Fin 2, if (i : ℕ) = 1 then c i else 0) = c 1
    rw [Fin.sum_univ_two]
    norm_num
  have hrad : polyDerivRadius c l u = 0 := by
    show (∑ i : Fin 2, if (i : ℕ) = 1 then 0
      else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)) = 0
    rw [Fin.sum_univ_two]
    norm_num
  show max |lo - polyDerivCenter c - polyDerivRadius c l u|
      |hi - polyDerivCenter c + polyDerivRadius c l u| = _
  rw [hctr, hrad, sub_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
