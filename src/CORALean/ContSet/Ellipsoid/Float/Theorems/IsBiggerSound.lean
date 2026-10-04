import CORALean.ContSet.Ellipsoid.Float.Operations.IsBigger
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
import CORALean.Global.Float.EuclideanNorm

/-!
# A `true` from `Ellipsoid.isBigger` proves the inclusion up to the centres

A point `q₂ + G₂ u + e` of `E₂`, moved by `-q₂`, is `G₁ (T u) + (Δ u + e)` with
`Δ = G₂ - G₁ T`: `T u` is in the unit ball (Cauchy–Schwarz per row, the Frobenius norm at most
`1`), `Δ u` within `generatorError` of the bracketed residual (`Ellipsoid.mem_generatorError`),
and `Δ u + e` in `E₁`'s box by the checked corners. So it is a point of `E₁` moved by `-q₁`:
`E₂ - q₂ ⊆ E₁ - q₁`, the inclusion the exact layer's `isBigger_iff_subset` characterises.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix of Frobenius norm at most `1` keeps the unit ball. -/
theorem Ellipsoid.aux_norm₂_mulVec_le_one {a b : ℕ} (T : Mat ℝ a b) (u : Vec ℝ b)
    (hT : ∑ i, ∑ j, T i j ^ 2 ≤ 1) (hu : ‖u‖₂ ≤ 1) :
    ‖fun i => ∑ j, T i j * u j‖₂ ≤ 1 := by -- --- PROOF ---
  -- each row's value is at most the row's length, by Cauchy–Schwarz
  have hrow : ∀ i, (∑ j, T i j * u j) ^ 2 ≤ ∑ j, T i j ^ 2 := fun i => by
    have h := abs_dotProduct_le_norm₂_mul_norm₂ (fun j => T i j) u
    have hn : ‖(fun j => T i j)‖₂ * ‖u‖₂ ≤ ‖(fun j => T i j)‖₂ :=
      mul_le_of_le_one_right (norm₂_nonneg _) hu
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (h.trans hn) 2
    rw [sq_abs, norm₂_sq] at h2
    exact h2
  have hsq : ‖fun i => ∑ j, T i j * u j‖₂ ^ 2 ≤ 1 ^ 2 := by
    rw [norm₂_sq, one_pow]
    exact le_trans (Finset.sum_le_sum fun i _ => hrow i) hT
  exact (pow_le_pow_iff_left₀ (norm₂_nonneg _) zero_le_one two_ne_zero).mp hsq


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isBigger_sound {E₁ E₂ : Ellipsoid 𝕋 n} {T : Mat 𝕋 E₁.k E₂.k}
    (h : E₁.isBigger E₂ T = true) :
    (fun x => x - toRealVec E₂.q) '' E₂.construct
      ⊆ (fun x => x - toRealVec E₁.q) '' E₁.construct := by -- --- PROOF ---
  simp only [Ellipsoid.isBigger, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hT, hbox⟩ := h
  rintro _ ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
  obtain ⟨u, hu, hyu⟩ := Ellipsoid.mem_nominalSet_iff.mp hy
  -- the factor `T u` stays in the unit ball
  set v : Vec ℝ E₁.k := fun l => ∑ j, toReal (T l j) * u j with hv
  have hvn : ‖v‖₂ ≤ 1 := by
    refine Ellipsoid.aux_norm₂_mulVec_le_one (fun l j => toReal (T l j)) u ?_ hu
    refine le_trans ?_ ((toReal_le_of_le hT).trans_eq toReal_one)
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
    exact sq_sum_le_sqSumUp fun j => by rw [toReal_absolute]
  -- the residual `Δ = G₂ - G₁ T`, entrywise within its rounded magnitude
  set Δ : Mat ℝ n E₂.k := fun i j =>
    toReal (E₂.G i j) - ∑ l, toReal (E₁.G i l) * toReal (T l j) with hΔ
  have hgap : ∀ i j, |Δ i j| ≤ toReal (maximum
      (subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j))
      (neg (subDown (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j)))) := fun i j => by
    rw [toReal_maximum, toReal_neg]
    have d₁ := le_dotUp (fun l => E₁.G i l) fun l => T l j
    have d₂ := dotDown_le (fun l => E₁.G i l) fun l => T l j
    have s₁ := subDown_le_sub (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j)
    have s₂ := sub_le_subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j)
    have m₁ := le_max_left (toReal (subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j)))
      (-toReal (subDown (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j)))
    have m₂ := le_max_right (toReal (subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j)))
      (-toReal (subDown (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j)))
    exact abs_le.mpr ⟨by simp only [hΔ]; linarith, by simp only [hΔ]; linarith⟩
  set gapF : Mat 𝕋 n E₂.k := fun i j => maximum
      (subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j))
      (neg (subDown (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j))) with hgapF
  have hres := Ellipsoid.mem_generatorError (G := gapF) hgap hu
  -- the residual's reach plus `E₂`'s box lies in `E₁`'s box
  have hbox' : (fun i => (∑ j, Δ i j * u j) + e i) ∈ E₁.err.construct := fun i => by
    have hr : toReal (neg (radius gapF i)) ≤ ∑ j, Δ i j * u j
        ∧ ∑ j, Δ i j * u j ≤ toReal (radius gapF i) := hres i
    have he' : toReal (E₂.err.inf i) ≤ e i ∧ e i ≤ toReal (E₂.err.sup i) := he i
    rw [toReal_neg] at hr
    have b₁ := toReal_le_of_le (hbox i).1
    have b₂ := toReal_le_of_le (hbox i).2
    have r₁ := subDown_le_sub (E₂.err.inf i) (radius gapF i)
    have r₂ := add_le_addUp (E₂.err.sup i) (radius gapF i)
    show toReal (E₁.err.inf i) ≤ (∑ j, Δ i j * u j) + e i
      ∧ (∑ j, Δ i j * u j) + e i ≤ toReal (E₁.err.sup i)
    exact ⟨by linarith, by linarith⟩
  -- the moved point is `G₁ v` plus that remainder, moved from `q₁`
  refine ⟨toRealVec E₁.q + ((fun i => ∑ l, toReal (E₁.G i l) * v l)
      + fun i => (∑ j, Δ i j * u j) + e i), ⟨fun i => toReal (E₁.q i)
      + ∑ l, toReal (E₁.G i l) * v l, Ellipsoid.mem_nominalSet_iff.mpr ⟨v, hvn, fun _ => rfl⟩,
      _, hbox', ?_⟩, ?_⟩
  · funext i
    simp only [Pi.add_apply, toRealVec]
    ring
  · funext i
    -- `G₁ (T u) + Δ u = G₂ u`, the two sums exchanged
    have hswap : ∑ l, toReal (E₁.G i l) * v l
        = ∑ j, (∑ l, toReal (E₁.G i l) * toReal (T l j)) * u j := by
      simp only [hv, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    have hres' : ∑ j, Δ i j * u j = ∑ j, toReal (E₂.G i j) * u j
        - ∑ j, (∑ l, toReal (E₁.G i l) * toReal (T l j)) * u j := by
      simp only [hΔ, sub_mul, Finset.sum_sub_distrib]
    simp only [Pi.add_apply, Pi.sub_apply, toRealVec, hyu i, hswap, hres']
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
