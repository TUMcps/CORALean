module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.taylor` encloses `g ∘ f`

The Lagrange remainder lemma at a Taylor model: for `g` smooth to order `N + 1`
between the center and the model's range, with `|g⁽ᴺ⁺¹⁾| ≤ D` there, the expansion encloses
`g ∘ f`. `taylor_remainder_abs_le` bounds the remainder by `D |f t - c|ᴺ⁺¹ / (N+1)!` and
`reach` bounds `|f t - c|`. This is the one lemma every elementary function reduces to: what
is left for each is its derivatives.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.taylor_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (g : ℝ → ℝ)
    (c D : ℝ)
    (hg : ∀ ξ ∈ Set.Icc (min c T.bounds.inf) (max c T.bounds.sup),
      ContDiffAt ℝ (T.maxOrder + 1) g ξ)
    (hD : ∀ ξ ∈ Set.Icc (min c T.bounds.inf) (max c T.bounds.sup),
      |iteratedDeriv (T.maxOrder + 1) g ξ| ≤ D) : -- --- CONCL ---
    (T.taylor g c D).Encloses fun t => g (f t) := by -- --- PROOF ---
  unfold Taylm.taylor
  refine Taylm.compose_outer h g c _ _ _ fun t ht => ?_
  have hb := Taylm.bounds_mem h ht
  -- the segment from the center to `f t` lies in the hull the hypotheses cover
  have hsub : Set.uIcc c (f t) ⊆ Set.Icc (min c T.bounds.inf) (max c T.bounds.sup) :=
    Set.uIcc_subset_Icc ⟨min_le_left _ _, le_max_left _ _⟩
      ⟨le_trans (min_le_right _ _) hb.1, le_trans hb.2 (le_max_right _ _)⟩
  have hL := taylor_remainder_abs_le (fun ξ hξ => hg ξ (hsub hξ)) (fun ξ hξ => hD ξ (hsub hξ))
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD c (hsub Set.left_mem_uIcc))
  have hy : |f t - c| ≤ T.reach c := by
    rw [Taylm.reach, abs_le]
    constructor
    · have := neg_abs_le (T.bounds.inf - c)
      have := le_max_left |T.bounds.inf - c| |T.bounds.sup - c|
      linarith [hb.1]
    · have := le_abs_self (T.bounds.sup - c)
      have := le_max_right |T.bounds.inf - c| |T.bounds.sup - c|
      linarith [hb.2]
  refine le_trans hL ?_
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
