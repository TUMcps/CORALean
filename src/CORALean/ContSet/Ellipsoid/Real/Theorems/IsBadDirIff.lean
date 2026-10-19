module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBadDir
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsUnitShape
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# A direction is bad iff the inner difference shape is not positive semidefinite

`priv_lminkDiff` approximates `E₁ ⊖ E₂` from inside along a good direction `l` by the ellipsoid of
shape `Q = (1 - 1/p) Q₁ + (1 - p) Q₂` with `p = sqrt(lᵀ Q₁ l)/sqrt(lᵀ Q₂ l)`. This `Q` is
positive semidefinite iff `p` is at most `1/λ`, `λ` the largest `vᵀ Q₂ v / vᵀ Q₁ v`, which is
`isBadDir` read in the negative: for `p > 1` it is `(p - 1)/p · (vᵀ Q₁ v - p vᵀ Q₂ v) ≥ 0` for
every `v`. So CORA's `r = 1/max(diag(D))` has no square root missing, and a bad direction is one
along which the inner shape fails to be a shape. Stated for `Q₁` of full rank, `Q₂ ⪯ Q₁`
(`isBigger`, which `minkDiff` checks first) and `lᵀ Q₂ l > 0`, with `Q` as its quadratic form.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The quadratic form of a shape is nonnegative. -/
theorem Ellipsoid.aux_quad_nonneg (E : Ellipsoid n) (v : Vec ℝ n) :
    0 ≤ v ⬝ᵥ (E.Q *ᵥ v) := by
  rw [Ellipsoid.quad_eq, dotProduct_self]
  positivity

/-- At full rank it is positive off zero. -/
theorem Ellipsoid.aux_quad_pos (E : Ellipsoid n) (hr : E.rank = n) {v : Vec ℝ n} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (E.Q *ᵥ v) := by -- --- PROOF ---
  refine (Ellipsoid.aux_quad_nonneg E v).lt_of_ne fun h => hv ?_
  -- a zero form gives `Gᵀ v = 0`, so `Q v = 0`, and `Q` is injective
  rw [Ellipsoid.quad_eq, eq_comm, dotProduct_self_eq_zero] at h
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (E.isUnit_shape hr)
  apply hinj
  rw [← E.G_mul_transpose, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, Matrix.mulVec_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isBadDir_iff (E₁ E₂ : Ellipsoid n) (l : Vec ℝ n) (p : ℝ)
    (hr : E₁.rank = n) (hbig : E₁.isBigger E₂) (hl : 0 < l ⬝ᵥ (E₂.Q *ᵥ l))
    (hp : p = Real.sqrt (l ⬝ᵥ (E₁.Q *ᵥ l)) / Real.sqrt (l ⬝ᵥ (E₂.Q *ᵥ l))) : -- --- CONCL ---
    E₁.isBadDir E₂ l ↔ ¬ ∀ v : Vec ℝ n, 0 ≤ (1 - 1 / p) * (v ⬝ᵥ (E₁.Q *ᵥ v))
      + (1 - p) * (v ⬝ᵥ (E₂.Q *ᵥ v)) := by -- --- PROOF ---
  -- `l` is nonzero, as its form is positive
  have hl0 : l ≠ 0 := fun h => by simp [h] at hl
  have hal : 0 < l ⬝ᵥ (E₁.Q *ᵥ l) := Ellipsoid.aux_quad_pos E₁ hr hl0
  haveI : Nonempty {v : Vec ℝ n // v ≠ 0} := ⟨⟨l, hl0⟩⟩
  -- the Rayleigh quotients lie in `(0, 1]` for `l`, in `[0, 1]` throughout
  have hle : ∀ v : {v : Vec ℝ n // v ≠ 0},
      (v.1 ⬝ᵥ (E₂.Q *ᵥ v.1)) / (v.1 ⬝ᵥ (E₁.Q *ᵥ v.1)) ≤ 1 := fun v =>
    (div_le_one (Ellipsoid.aux_quad_pos E₁ hr v.2)).mpr (hbig v.1)
  have hbdd : BddAbove (Set.range fun v : {v : Vec ℝ n // v ≠ 0} =>
      (v.1 ⬝ᵥ (E₂.Q *ᵥ v.1)) / (v.1 ⬝ᵥ (E₁.Q *ᵥ v.1))) := ⟨1, by
    rintro _ ⟨v, rfl⟩; exact hle v⟩
  set lam : ℝ := ⨆ v : {v : Vec ℝ n // v ≠ 0},
    (v.1 ⬝ᵥ (E₂.Q *ᵥ v.1)) / (v.1 ⬝ᵥ (E₁.Q *ᵥ v.1)) with hlam
  have hlam1 : lam ≤ 1 := ciSup_le hle
  have hlampos : 0 < lam :=
    lt_of_lt_of_le (div_pos hl hal) (le_ciSup hbdd (⟨l, hl0⟩ : {v : Vec ℝ n // v ≠ 0}))
  -- `p ≥ 1`
  have hsa : 0 < Real.sqrt (l ⬝ᵥ (E₁.Q *ᵥ l)) := Real.sqrt_pos.mpr hal
  have hsb : 0 < Real.sqrt (l ⬝ᵥ (E₂.Q *ᵥ l)) := Real.sqrt_pos.mpr hl
  have hp1 : 1 ≤ p := by
    rw [hp, le_div_iff₀ hsb, one_mul]
    exact Real.sqrt_le_sqrt (hbig l)
  have hppos : 0 < p := by linarith
  -- the verdict reads `1/λ < p`
  have hbad : E₁.isBadDir E₂ l ↔ 1 / lam < p := by
    unfold Ellipsoid.isBadDir
    rw [hp]
  -- the form of the shape is nonnegative iff every quotient is at most `1/p`
  rw [hbad]
  rcases hp1.eq_or_lt with h1 | h1
  · -- `p = 1`: the shape is zero and `λ ≤ 1` is not bad
    rw [← h1]
    simp only [div_one, sub_self, zero_mul, add_zero, le_refl, implies_true, not_true_eq_false,
      iff_false, not_lt]
    exact (one_le_one_div hlampos hlam1)
  · -- `p > 1`
    have hp0 : 0 < p - 1 := by linarith
    -- the form factors as `(p - 1) (vᵀ Q₁ v / p - vᵀ Q₂ v)`
    have hform : ∀ v : Vec ℝ n, (1 - 1 / p) * (v ⬝ᵥ (E₁.Q *ᵥ v))
        + (1 - p) * (v ⬝ᵥ (E₂.Q *ᵥ v))
        = (p - 1) * ((v ⬝ᵥ (E₁.Q *ᵥ v)) / p - (v ⬝ᵥ (E₂.Q *ᵥ v))) := fun v => by
      field_simp
      ring
    have hiff : (∀ v : Vec ℝ n, 0 ≤ (1 - 1 / p) * (v ⬝ᵥ (E₁.Q *ᵥ v))
        + (1 - p) * (v ⬝ᵥ (E₂.Q *ᵥ v))) ↔ lam ≤ 1 / p := by
      simp only [hform]
      constructor
      · -- a nonnegative form bounds every quotient by `1/p`, so their supremum
        intro h
        refine ciSup_le fun v => ?_
        have hv := h v.1
        have hapos := Ellipsoid.aux_quad_pos E₁ hr v.2
        rw [div_le_iff₀ hapos]
        have := (mul_nonneg_iff_of_pos_left hp0).mp hv
        rw [one_div, inv_mul_eq_div]
        linarith
      · -- the supremum at most `1/p` bounds each `vᵀ Q₂ v` by `vᵀ Q₁ v / p`
        intro h v
        refine mul_nonneg hp0.le ?_
        by_cases hv : v = 0
        · simp [hv]
        · have hq := (le_ciSup hbdd (⟨v, hv⟩ : {v : Vec ℝ n // v ≠ 0})).trans h
          have hapos := Ellipsoid.aux_quad_pos E₁ hr hv
          rw [div_le_iff₀ hapos, one_div] at hq
          rw [sub_nonneg]
          calc v ⬝ᵥ (E₂.Q *ᵥ v) ≤ p⁻¹ * (v ⬝ᵥ (E₁.Q *ᵥ v)) := by linarith
            _ = (v ⬝ᵥ (E₁.Q *ᵥ v)) / p := by rw [inv_mul_eq_div]
    -- bad is `1/λ < p`, that is `1/p < λ`, the negation of `λ ≤ 1/p`
    rw [hiff, not_le]
    rw [div_lt_iff₀ hlampos, one_div, inv_lt_iff_one_lt_mul₀ hppos]
    constructor <;> intro h <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
