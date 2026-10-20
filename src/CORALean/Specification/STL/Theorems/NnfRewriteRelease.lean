module

public import CORALean.Specification.STL.Definitions.NnfRewrite
public import CORALean.Specification.STL.Theorems.RewriteReleaseSucc
public import CORALean.Specification.STL.Theorems.RewriteReleaseZero
public import CORALean.Specification.STL.Theorems.RewriteFinOpenReleaseSucc
public import CORALean.Specification.STL.Theorems.RewriteFinOpenReleaseZero
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenReleaseSucc
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenReleaseZero
public import CORALean.Specification.STL.Theorems.ReleaseZeroEquiv
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatOr

@[expose] public section

/-!
# A release rewrites to sampled time

[1, Lemma 4]: `φ R[i,j] ψ` rewrites if `φ`, `ψ`, `φ ∧ ψ` (when `j ≥ 1`) and every `φ R[i',j'] ψ`
with `j' < j` do, by [1, Table 1]'s `R` rows in the three contexts, `R[0,0] ≡ ψ` and, for an empty
interval, `⊥`. The `F_I` row of `R[0,j]` is the one that asks for `F_I(φ ∧ ψ)`.

## Inputs
* `i` – interval lower bound
* `j` – interval upper bound
* `φ` – left formula
* `ψ` – right formula

## Hypotheses
* `hφ` – the left formula rewrites to sampled time
* `hψ` – the right formula rewrites to sampled time
* `hand` – the conjunction rewrites if the bound is positive
* `hrec` – smaller releases rewrite to sampled time

## Conclusion
* the release rewrites to sampled time

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Nnf.hasSampledRewrite_release (i j : ℕ) {φ ψ : STL.Nnf X} (hφ : φ.HasSampledRewrite)
    (hψ : ψ.HasSampledRewrite) (hand : 1 ≤ j → (STL.Nnf.and φ ψ).HasSampledRewrite)
    (hrec : ∀ j' < j, ∀ i', (STL.Nnf.release i' j' φ ψ).HasSampledRewrite) : -- --- CONCL ---
    (STL.Nnf.release i j φ ψ).HasSampledRewrite := by -- --- PROOF ---
  obtain ⟨⟨sTφ, hTφ⟩, ⟨sFφ, hFφ⟩, ⟨sGφ, hGφ⟩⟩ := hφ
  obtain ⟨⟨sTψ, hTψ⟩, ⟨sFψ, hFψ⟩, ⟨sGψ, hGψ⟩⟩ := hψ
  by_cases hji : j < i
  · -- an empty interval: `⊥` implies everything
    have hbot : ∀ ξ, ¬ ((STL.Samp.lit (Pform.bot : Pform X)).toFormula 1).Sat ξ :=
      fun ξ h => (h : False)
    exact ⟨⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩,
      ⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩,
      ⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `φ R[0,0] ψ ≡ ψ`, in each context
    obtain rfl : i = 0 := by omega
    have e : ∀ ξ : ℝ≥0 → X, (STL.Nnf.release 0 0 φ ψ).toFormula.Sat ξ ↔ ψ.toFormula.Sat ξ := by
      intro ξ
      simpa only [STL.Nnf.toFormula, Nat.cast_zero] using
        STL.release_zero_equiv φ.toFormula ψ.toFormula ξ
    refine ⟨⟨sTψ, fun ξ h => (e ξ).2 (hTψ ξ h)⟩, ⟨sFψ, fun ξ h => ?_⟩, ⟨sGψ, fun ξ h => ?_⟩⟩
    · obtain ⟨t, h₀, h₁, ht⟩ := hFψ ξ h
      exact ⟨t, h₀, h₁, (e _).2 ht⟩
    · exact fun t h₀ h₁ => (e _).2 (hGψ ξ h t h₀ h₁)
  by_cases hi : i = 0
  · subst hi
    obtain ⟨-, ⟨sFa, hFa⟩, -⟩ := hand hj
    obtain ⟨⟨sT, hT⟩, ⟨sF, hF⟩, ⟨sG, hG⟩⟩ := hrec (j - 1) (by omega) 0
    simp only [STL.Nnf.toFormula, Nat.cast_zero] at hT hF hG
    refine ⟨⟨.and sTψ (.or sTφ (.and sGψ (.or sFφ (.next sT)))), fun ξ h => ?_⟩,
      ⟨.or sFa (.and sGψ (.next (.and sTψ (.or sTφ (.and sGψ sF))))), fun ξ h => ?_⟩,
      ⟨.and sGψ (.or sGφ (.next (.and sTψ (.or sTφ (.and sGψ sG))))), fun ξ h => ?_⟩⟩
    · -- row `R[0,j]`
      have := STL.rewrite_release_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next,
        STL.Formula.sat_or] at h ⊢
      exact ⟨hTψ ξ h.1, h.2.imp (hTφ ξ) fun ⟨a, b⟩ => ⟨hGψ ξ a, b.imp (hFφ ξ) (hT _)⟩⟩
    · -- row `F_I` of `R[0,j]`
      have := STL.rewrite_finOpen_release_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next,
        STL.Formula.sat_or] at h ⊢
      refine h.imp (hFa ξ) fun ⟨a, b⟩ => ⟨hGψ ξ a, hTψ _ b.1, b.2.imp (hTφ _) ?_⟩
      exact fun ⟨c, d⟩ => ⟨hGψ _ c, hF _ d⟩
    · -- row `G_I` of `R[0,j]`
      have := STL.rewrite_globOpen_release_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next,
        STL.Formula.sat_or] at h ⊢
      refine ⟨hGψ ξ h.1, h.2.imp (hGφ ξ) fun a => ⟨hTψ _ a.1, a.2.imp (hTφ _) ?_⟩⟩
      exact fun ⟨c, d⟩ => ⟨hGψ _ c, hG _ d⟩
  · -- `i ≥ 1`
    obtain ⟨⟨sT, hT⟩, ⟨sF, hF⟩, ⟨sG, hG⟩⟩ := hrec (j - 1) (by omega) (i - 1)
    have hi1 : 1 ≤ i := by omega
    have hij : i ≤ j := by omega
    refine ⟨⟨.or sTφ (.or sFφ (.next sT)), fun ξ h => ?_⟩,
      ⟨.or sFφ (.next (.or sTφ (.or sFφ sF))), fun ξ h => ?_⟩,
      ⟨.or sGφ (.next (.or sTφ sG)), fun ξ h => ?_⟩⟩
    · -- row `R[i,j]`
      refine STL.rewrite_release_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_next, STL.Formula.sat_or] at h ⊢
      exact h.imp (hTφ ξ) fun h => h.imp (hFφ ξ) (hT _)
    · -- row `F_I` of `R[i,j]`
      refine STL.rewrite_finOpen_release_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_next, STL.Formula.sat_or] at h ⊢
      exact h.imp (hFφ ξ) fun h => h.imp (hTφ _) fun h => h.imp (hFφ _) (hF _)
    · -- row `G_I` of `R[i,j]`
      refine STL.rewrite_globOpen_release_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_next, STL.Formula.sat_or] at h ⊢
      exact h.imp (hGφ ξ) fun h => h.imp (hTφ _) (hG _)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
