import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A box as a polynomial zonotope

The box's zonotope, then that zonotope's factors: one dependent factor per
coordinate and no independent generators. Nothing is lost by either step, but
only the enclosing direction is stated, since `Interval.zonotope` states only
that — a box whose `sup` falls below its `inf` denotes nothing while the
zonotope built from it does not.

This is how a reachability run starts from a box without leaving the
representation it will stay in.

`polyZonotope_norm_le` is the other direction in the only form that survives the
swap: not an inclusion in the box, but a bound in the supremum norm, and it asks
for *both* ends to be small rather than for the box to be ordered. That is what
a residual block contributes to a Minkowski inflation.

`polyZonotope_mono` is monotone in the two ends, the narrower box having to be
ordered for the same reason.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.polyZonotope (I : Interval (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  I.zonotope.polyZonotope

theorem Interval.polyZonotope_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.polyZonotope.construct :=
  subset_trans I.zonotope_contains (Zonotope.polyZonotope_exact _).subset


-- =======================================  MAIN THEOREM  ======================================= --

/-- With both ends inside `[-ε, ε]` the whole set is, whichever way round the
box is: a coordinate is a convex combination of its two ends. -/
theorem Interval.polyZonotope_norm_le {I : Interval (Vec ℝ n)} {ε : ℝ} (hε : 0 ≤ ε)
    (hlo : ∀ i, |I.inf i| ≤ ε) (hhi : ∀ i, |I.sup i| ≤ ε) {y : Vec ℝ n}
    (hy : y ∈ I.polyZonotope.construct) : ‖y‖ ≤ ε := by -- --- PROOF ---
  have hz : y ∈ I.zonotope.construct := by
    rw [Zonotope.polyZonotope_exact]
    exact hy
  obtain ⟨β, hβ, rfl⟩ := hz
  rw [pi_norm_le_iff_of_nonneg hε]
  intro i
  -- only the diagonal generator `i` reaches coordinate `i`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  show ‖((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
    (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i‖ ≤ ε
  rw [Pi.add_apply, hsum, Real.norm_eq_abs, abs_le]
  obtain ⟨hb1, hb2⟩ := abs_le.mp (hβ i)
  obtain ⟨hi1, hi2⟩ := abs_le.mp (hlo i)
  obtain ⟨hs1, hs2⟩ := abs_le.mp (hhi i)
  -- the two ends carry weights `(1 ± β) / 2`, both nonnegative and summing to one
  constructor
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + β i by linarith)
      (show (0:ℝ) ≤ I.sup i + ε by linarith),
      mul_nonneg (show (0:ℝ) ≤ 1 - β i by linarith)
        (show (0:ℝ) ≤ I.inf i + ε by linarith)]
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + β i by linarith)
      (show (0:ℝ) ≤ ε - I.sup i by linarith),
      mul_nonneg (show (0:ℝ) ≤ 1 - β i by linarith)
        (show (0:ℝ) ≤ ε - I.inf i by linarith)]

/-- A box inside a wider one, as polynomial zonotopes: the wider box already
holds every point the narrower one's enclosure reaches. -/
theorem Interval.polyZonotope_mono {I₁ I₂ : Interval (Vec ℝ n)}
    (hord : ∀ i, I₁.inf i ≤ I₁.sup i) (hlo : ∀ i, I₂.inf i ≤ I₁.inf i)
    (hhi : ∀ i, I₁.sup i ≤ I₂.sup i) :
    I₁.polyZonotope.construct ⊆ I₂.polyZonotope.construct := by -- --- PROOF ---
  simp only [Interval.polyZonotope, ← Zonotope.polyZonotope_exact]
  rintro _ ⟨β, hβ, rfl⟩
  refine I₂.zonotope_contains ?_
  intro i
  -- only the diagonal generator `i` reaches coordinate `i`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I₁.sup i - I₁.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I₁.sup i - I₁.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  have hval : Entrywise.entry (I₁.zonotope.c + ∑ j, β j • I₁.zonotope.G j) i
      = (I₁.inf i + I₁.sup i) / 2 + β i * ((I₁.sup i - I₁.inf i) / 2) := by
    show ((fun i => (I₁.inf i + I₁.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I₁.sup i - I₁.inf i) / 2 else 0 : Vec ℝ n)) i = _
    rw [Pi.add_apply, hsum]
  -- the coordinate is its own centre plus at most its own radius, either way
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hβ i)
  have hrad : 0 ≤ (I₁.sup i - I₁.inf i) / 2 := by linarith [hord i]
  rw [hval, Entrywise.entry_vec, Entrywise.entry_vec]
  exact ⟨by nlinarith [hlo i], by nlinarith [hhi i]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
