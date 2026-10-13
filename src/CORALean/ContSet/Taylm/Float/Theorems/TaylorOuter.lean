module

public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.taylor` encloses `g ∘ f`

The Lagrange remainder lemma at a float Taylor model: `g` smooth to order `N + 1` between the
centre and the model's range, `|g⁽ᴺ⁺¹⁾| ≤ D` there for a real `D` below the rounded `Dup`, and
the coefficient enclosures around `g⁽ᵏ⁾(c) / k!`. `taylor_remainder_abs_le` bounds the remainder
by `D |f t - c|ᴺ⁺¹ / (N+1)!`, and each factor is below its rounded counterpart.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.taylor_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (g : ℝ → ℝ)
    (c : 𝕋) (lo hi : ℕ → 𝕋) (Dup : 𝕋) (D : ℝ)
    (hc : ∀ k ≤ T.maxOrder, toReal (lo k) ≤ iteratedDeriv k g (toReal c) / (k.factorial : ℝ) ∧
      iteratedDeriv k g (toReal c) / (k.factorial : ℝ) ≤ toReal (hi k))
    (hg : ∀ ξ ∈ Set.Icc (min (toReal c) (toReal T.bounds.1)) (max (toReal c) (toReal T.bounds.2)),
      ContDiffAt ℝ (T.maxOrder + 1) g ξ)
    (hD : ∀ ξ ∈ Set.Icc (min (toReal c) (toReal T.bounds.1)) (max (toReal c) (toReal T.bounds.2)),
      |iteratedDeriv (T.maxOrder + 1) g ξ| ≤ D)
    (hDup : D ≤ toReal Dup) :
    (T.taylor c lo hi Dup).Encloses fun t => g (f t) := by -- --- PROOF ---
  set N := T.maxOrder
  refine Taylm.compose_outer h g c lo hi N _
    (fun k => iteratedDeriv k g (toReal c) / (k.factorial : ℝ)) hc fun t ht => ?_
  -- the segment from the centre to `f t` lies in the hull the hypotheses cover
  have hb := Taylm.bounds_mem h ht
  have hsub : Set.uIcc (toReal c) (f t) ⊆
      Set.Icc (min (toReal c) (toReal T.bounds.1)) (max (toReal c) (toReal T.bounds.2)) :=
    Set.uIcc_subset_Icc ⟨min_le_left _ _, le_max_left _ _⟩
      ⟨le_trans (min_le_right _ _) hb.1, le_trans hb.2 (le_max_right _ _)⟩
  have hL := taylor_remainder_abs_le (g := g) (N := N) (c := toReal c) (x := f t) (D := D)
    (fun ξ hξ => hg ξ (hsub hξ)) fun ξ hξ => hD ξ (hsub hξ)
  refine le_trans hL ?_
  -- `|f t - c|` below the rounded reach
  set B : 𝕋 := maximum zero (maximum (subUp T.bounds.2 c) (subUp c T.bounds.1))
  have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
  have hPow := le_powUp (abs_nonneg _) hB (N + 1)
  -- each factor of the bound below its rounded counterpart
  have hE : 0 ≤ D := le_trans (abs_nonneg _) (hD (toReal c) (hsub Set.left_mem_uIcc))
  have hF := (divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
  have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
  have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
  calc D * |f t - toReal c| ^ (N + 1) / ((N + 1).factorial : ℝ)
      = D * |f t - toReal c| ^ (N + 1) * (1 / ((N + 1).factorial : ℝ)) := by ring
    _ ≤ toReal Dup * toReal (powUp B (N + 1))
        * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
      apply mul_le_mul (mul_le_mul hDup hPow hY (le_trans hE hDup)) hF hFpos
      exact mul_nonneg (le_trans hE hDup) (le_trans hY hPow)
    _ ≤ toReal (mulUp Dup (powUp B (N + 1)))
        * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) (le_trans hFpos hF)
    _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
