module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PsdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.SymmOfIsSymm

@[expose] public section

/-!
# A `true` from `Ellipsoid.isBigger` proves the inclusion up to the centers

`Q₁ - Q₂`, read as reals, is symmetric and lies in the checked interval matrix, so it is positive
semi-definite (`posSemidef_of_psdCheck`): `Q₁` dominates `E₂`'s nominal shape (`Q₂`, or `0` where
`Q₂` is refused), so a point `q₂ + y` of `E₂`'s nominal part gives the point `q₁ + y` of `E₁`'s
(`add_sub_mem_nominalSet`), and `E₂`'s error box lies in `E₁`'s by the checked corners. So
`E₂ - q₂ ⊆ E₁ - q₁`, the inclusion the exact layer's `isBigger_iff_subset` characterises.

## Inputs
* `E₁` – larger ellipsoid
* `E₂` – smaller ellipsoid

## Hypotheses
* `h` – `isBigger` returns `true`

## Conclusion
* `E₂` centered at the origin lies in `E₁` centered at the origin
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix of Frobenius norm at most `1` keeps the unit ball. -/
theorem Ellipsoid.aux_norm₂_mulVec_le_one {a b : ℕ} (T : Mat ℝ a b) (u : Vec ℝ b)
    (hT : ∑ i, ∑ j, T i j ^ 2 ≤ 1) (hu : ‖u‖₂ ≤ 1) : -- --- CONCL ---
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

theorem Ellipsoid.isBigger_sound {E₁ E₂ : Ellipsoid 𝕋 n}
    (h : E₁.isBigger E₂ = true) : -- --- CONCL ---
    (fun x => x - toRealVec E₂.q) '' E₂.construct
      ⊆ (fun x => x - toRealVec E₁.q) '' E₁.construct := by -- --- PROOF ---
  simp only [Ellipsoid.isBigger, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨hs₁, hs₂⟩, hc⟩, hbox⟩ := h
  -- `Q₁ - Q₂` is positive semi-definite
  have hD : (toRealMat E₁.Q - toRealMat E₂.Q).PosSemidef := by
    refine Ellipsoid.posSemidef_of_psdCheck hc (fun i j => ⟨?_, ?_⟩) fun i j => ?_
    · exact subDown_le_sub (E₁.Q i j) (E₂.Q i j)
    · exact sub_le_subUp (E₁.Q i j) (E₂.Q i j)
    · show toReal (E₁.Q i j) - toReal (E₂.Q i j) = toReal (E₁.Q j i) - toReal (E₂.Q j i)
      rw [Ellipsoid.symm_of_isSymm hs₁, Ellipsoid.symm_of_isSymm hs₂]
  -- so `Q₁` dominates `E₂`'s nominal shape
  have hF : (nominal E₂).ellipsoid.Q = 0
      ∨ (toRealMat E₁.Q - (nominal E₂).ellipsoid.Q).PosSemidef := by
    rw [Ellipsoid.nominal_Q_eq]
    split_ifs
    · exact Or.inr hD
    · exact Or.inl rfl
  rintro _ ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
  have hy' := Ellipsoid.add_sub_mem_nominalSet hF hy
  refine ⟨_, ⟨_, hy', e, fun i => ?_, rfl⟩, ?_⟩
  · -- `E₂`'s box inside `E₁`'s
    obtain ⟨h₁, h₂⟩ := hbox i
    exact ⟨le_trans (toReal_le_of_le h₁) (he i).1, le_trans (he i).2 (toReal_le_of_le h₂)⟩
  · rw [E₂.nominal_q]
    show toRealVec E₁.q + (y - toRealVec E₂.q) + e - toRealVec E₁.q = y + e - toRealVec E₂.q
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
