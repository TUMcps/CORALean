module

public import CORALean.ContSet.Zonotope.Float.Operations.RightInvGain
public import CORALean.ContSet.Zonotope.Float.Theorems.RightInvQBound
public import CORALean.Global.MulVecInjectiveOfResidual
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `Zonotope.rightInvGain` bounds a solution of every system

The real statement first: if every row of `1 - G H` has absolute sum at most `κ < 1`, for a
`G : q × n` and an `H : n × q` trusted for nothing, then every right-hand side `d` with `|dᵢ| ≤ ε`
is `G β` for a `β` with `|βⱼ| ≤ (∑ₖ |Hⱼₖ|) ε / (1 - κ)`. This is the Neumann bound
`‖(G H)⁻¹‖ ≤ 1 / (1 - κ)` in the sup norm, without the series: `G H` is injective
(`mulVec_injective_of_residual`), so invertible, and its solution `w` of `G H w = d` satisfies
`w = d + (1 - G H) w`, which at the largest coordinate gives `|w| ≤ ε + κ |w|`. Then `β = H w`.

Read as reals, an accepted certificate is its hypothesis: the row sums of `|1 - G H|` are below
`κ = rightInvQ G H`, and `1 - κ` is above the positive `d` the check saw. The bound is then below
`γ ε`, the row sum below the largest one and `1 - κ` above `d`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The real statement: a checked approximate right inverse solves, with a bound. -/
private theorem exists_mulVec_eq_of_residual (G : Mat ℝ q n) (H : Mat ℝ n q)
    {κ ε : ℝ} (hκ : κ < 1) (hK : ∀ i, ∑ j, |((1 : Mat ℝ q q) - G * H) i j| ≤ κ)
    (d : Vec ℝ q) (hd : ∀ i, |d i| ≤ ε) :
    ∃ β : Vec ℝ n, G *ᵥ β = d ∧ ∀ j, |β j| ≤ (∑ k, |H j k|) * (ε / (1 - κ)) := by -- --- PROOF ---
  -- `G H` is invertible: injective, and square
  set Pm := G * H with hPm
  have hinj : Function.Injective Pm.mulVec :=
    mulVec_injective_of_residual 1 Pm fun i => by
      simpa only [Matrix.one_mul] using lt_of_le_of_lt (hK i) hκ
  have hdet : IsUnit Pm.det :=
    (isUnit_iff_isUnit_det Pm).mp (mulVec_injective_iff_isUnit.mp hinj)
  set w := Pm⁻¹ *ᵥ d with hwdef
  have hw : Pm *ᵥ w = d := by
    rw [hwdef, mulVec_mulVec, mul_nonsing_inv Pm hdet, one_mulVec]
  -- the bound on `w`, at its largest coordinate: `w = d + (1 - G H) w`
  have hwB : ∀ k, |w k| ≤ ε / (1 - κ) := by
    rcases isEmpty_or_nonempty (Fin q) with hq | hq
    · exact fun k => (IsEmpty.false k).elim
    have hwK : w = d + (1 - Pm) *ᵥ w := by
      rw [sub_mulVec, one_mulVec, hw]
      abel
    obtain ⟨k, -, hk⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |w i|) Finset.univ_nonempty
    -- the contraction shrinks the largest coordinate by `κ`
    have hcon : |((1 - Pm) *ᵥ w) k| ≤ κ * |w k| := by
      calc |((1 - Pm) *ᵥ w) k| = |∑ j, (1 - Pm) k j * w j| := rfl
        _ ≤ ∑ j, |(1 - Pm) k j * w j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |(1 - Pm) k j| * |w k| := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hk j (Finset.mem_univ j)) (abs_nonneg _)
        _ = (∑ j, |(1 - Pm) k j|) * |w k| := (Finset.sum_mul _ _ _).symm
        _ ≤ κ * |w k| := mul_le_mul_of_nonneg_right (hK k) (abs_nonneg _)
    -- and `|w| ≤ |d| + κ |w|` there
    have hsplit : |w k| ≤ |d k| + |((1 - Pm) *ᵥ w) k| := by
      calc |w k| = |d k + ((1 - Pm) *ᵥ w) k| := by
            conv_lhs => rw [hwK]
            rfl
        _ ≤ _ := abs_add_le _ _
    have h1 : 0 < 1 - κ := by linarith
    have hk' : |w k| ≤ ε / (1 - κ) := by
      rw [le_div_iff₀ h1]
      nlinarith [hd k]
    exact fun j => le_trans (hk j (Finset.mem_univ j)) hk'
  -- `β = H w`
  refine ⟨H *ᵥ w, by rw [mulVec_mulVec, hw], fun j => ?_⟩
  calc |(H *ᵥ w) j| = |∑ k, H j k * w k| := rfl
    _ ≤ ∑ k, |H j k * w k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |H j k| * (ε / (1 - κ)) := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hwB k) (abs_nonneg _)
    _ = (∑ k, |H j k|) * (ε / (1 - κ)) := (Finset.sum_mul _ _ _).symm


theorem Zonotope.rightInvGain_solve {G : Mat 𝕋 q n} {H : Mat 𝕋 n q} {γ : 𝕋}
    (hγ : Zonotope.rightInvGain G H = some γ) :
    0 ≤ toReal γ ∧ ∀ (d : Vec ℝ q) {ε : ℝ}, 0 ≤ ε → (∀ i, |d i| ≤ ε) →
      ∃ β : Vec ℝ n, toRealMat G *ᵥ β = d ∧ ∀ j, |β j| ≤ toReal γ * ε := by -- --- PROOF ---
  unfold Zonotope.rightInvGain at hγ
  set κ := Zonotope.rightInvQ G H
  set dd := subDown (one : 𝕋) κ
  by_cases hc : ltStrict (zero : 𝕋) dd = true
  · rw [if_pos hc, Option.some.injEq] at hγ
    subst hγ
    -- `0 < d ≤ 1 - κ`
    have hd0 : 0 < toReal dd := by simpa [toReal_zero] using toReal_lt_of_ltStrict hc
    have hd1 : toReal dd ≤ 1 - toReal κ := by
      simpa [toReal_one] using subDown_le_sub (one : 𝕋) κ
    -- the largest row sum of `|H|` bounds each one, and is not negative
    have hrow : ∀ j, ∑ k, |toReal (H j k)| ≤ toReal (maximumOver (radius H)) := fun j =>
      le_trans (sum_abs_le_radius j) (le_maximumOver _ j)
    have hR0 : 0 ≤ toReal (maximumOver (radius H)) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [maximumOver, toReal_zero]
      · exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hrow ⟨0, hn⟩)
    have hγd : toReal (maximumOver (radius H)) / toReal dd
        ≤ toReal (divUp (maximumOver (radius H)) dd) := div_le_divUp _ _ hd0
    refine ⟨le_trans (div_nonneg hR0 hd0.le) hγd, fun d ε hε hdε => ?_⟩
    obtain ⟨β, hβ, hβB⟩ := exists_mulVec_eq_of_residual (toRealMat G) (toRealMat H)
      (κ := toReal κ) (by linarith) (fun i => Zonotope.rightInvQ_bound G H i) d hdε
    refine ⟨β, hβ, fun j => le_trans (hβB j) ?_⟩
    -- `(∑ₖ |Hⱼₖ|) ε / (1 - κ) ≤ R ε / d ≤ γ ε`
    have hS : ∑ k, |toRealMat H j k| ≤ toReal (maximumOver (radius H)) := hrow j
    have hS0 : 0 ≤ ∑ k, |toRealMat H j k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc (∑ k, |toRealMat H j k|) * (ε / (1 - toReal κ))
        ≤ toReal (maximumOver (radius H)) * (ε / toReal dd) :=
          mul_le_mul hS (div_le_div_of_nonneg_left hε hd0 hd1)
            (div_nonneg hε (by linarith)) hR0
      _ = toReal (maximumOver (radius H)) / toReal dd * ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hγd hε
  · rw [if_neg hc] at hγ
    exact absurd hγ (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
