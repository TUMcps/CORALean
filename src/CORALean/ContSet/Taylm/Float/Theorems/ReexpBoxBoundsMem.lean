import CORALean.ContSet.Taylm.Float.Operations.ReexpBoxBounds
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoxBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.ReexpandOuter
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem

/-!
# `Taylm.reexpBoxBounds` brackets the polynomial

On a box `B` the polynomial of a term list lies in the stored range. Where the re-expansion is
certified, the point is written in the normalized coordinates `s` of the midpoint and radius,
which lie in `[-1, 1]ⁿ`, and the float `reexpand_outer` and `bounds_mem` bracket the value;
otherwise the range is `polyBoxBounds`'s.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reexpBoxBounds_mem (P : List (𝕋 × (Fin n → ℕ))) {B : Fin n → 𝕋 × 𝕋} {t : Vec ℝ n}
    (ht : Taylm.InBox B t) :
    toReal (Taylm.reexpBoxBounds P B).1 ≤ Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.reexpBoxBounds P B).2 := by -- --- PROOF ---
  unfold Taylm.reexpBoxBounds
  dsimp only
  split_ifs with hc
  swap
  · exact Taylm.polyBoxBounds_mem P ht
  -- the midpoint and radius reach both ends of the box
  have hr : ∀ k, toReal (B k).2 - toReal (Taylm.boxMid B k) ≤ toReal (Taylm.boxRad B k) ∧
      toReal (Taylm.boxMid B k) - toReal (B k).1 ≤ toReal (Taylm.boxRad B k) := by
    intro k
    have h1 := sub_le_subUp (B k).2 (Taylm.boxMid B k)
    have h2 := sub_le_subUp (Taylm.boxMid B k) (B k).1
    simp only [Taylm.boxRad, toReal_maximum]
    exact ⟨le_trans h1 (le_max_left _ _), le_trans h2 (le_max_right _ _)⟩
  -- the certified `|m| + |r| ≤ 1`
  have hmr : ∀ k, |toReal (Taylm.boxMid B k)| + |toReal (Taylm.boxRad B k)| ≤ 1 := by
    intro k
    have h1 := toReal_le_of_le ((List.all_eq_true.1 hc) k (List.mem_finRange k))
    have h2 := add_le_addUp (absolute (Taylm.boxMid B k)) (absolute (Taylm.boxRad B k))
    rw [toReal_absolute, toReal_absolute] at h2
    rw [toReal_one] at h1
    linarith
  -- the normalized coordinates of `t`
  set s : Vec ℝ n := fun k =>
    if toReal (Taylm.boxRad B k) = 0 then 0
    else (t k - toReal (Taylm.boxMid B k)) / toReal (Taylm.boxRad B k) with hs_def
  have hts : (fun k => toReal (Taylm.boxMid B k) + toReal (Taylm.boxRad B k) * s k) = t := by
    funext k
    simp only [s]
    split_ifs with h0
    · have := ht k
      have := hr k
      rw [h0] at this
      linarith [(ht k).1, (ht k).2]
    · field_simp
      ring
  -- and they lie in the normalized box
  have hs : s ∈ Real.Taylm.box n := by
    intro k
    simp only [s]
    split_ifs with h0
    · simp
    · have h := ht k
      have h' := hr k
      have hr0 : 0 < toReal (Taylm.boxRad B k) :=
        lt_of_le_of_ne (by linarith [h.1, h.2, h'.1]) (Ne.symm h0)
      rw [abs_div, abs_of_pos hr0, div_le_one hr0, abs_le]
      constructor <;> linarith [h.1, h.2, h'.1, h'.2]
  -- the model of the term list with remainder `0` encloses its polynomial
  have hT0 : (⟨P, zero, zero, 0⟩ : Taylm 𝕋 n).Encloses
      fun s => Real.Taylm.polyOf (P.map fun a => (toReal a.1, a.2)) s := by
    intro s _
    simp only [Taylm.nominal, Real.Taylm.poly, toReal_zero, sub_self]
    exact ⟨le_rfl, le_rfl⟩
  have hre := Taylm.reexpand_outer hT0 (Taylm.boxMid B) (Taylm.boxRad B) hmr
  have hb := Taylm.bounds_mem hre hs
  rw [hts] at hb
  exact hb

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
