module

public import CORALean.Specification.STL.Definitions.NnfRewrite
public import CORALean.Specification.STL.Theorems.RewriteUntilSucc
public import CORALean.Specification.STL.Theorems.RewriteUntilZero
public import CORALean.Specification.STL.Theorems.RewriteFinOpenUntilSucc
public import CORALean.Specification.STL.Theorems.RewriteFinOpenUntilZero
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenUntilSucc
public import CORALean.Specification.STL.Theorems.RewriteGlobOpenUntilZero
public import CORALean.Specification.STL.Theorems.UntilZeroEquiv
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatOr

@[expose] public section

/-!
# An until rewrites to sampled time

[1, Lemma 4]: `φ U[i,j] ψ` rewrites if `φ`, `ψ` and every `φ U[i',j'] ψ` with `j' < j` do, by [1,
Table 1]'s `U` rows in the three contexts, `U[0,0] ≡ ψ` and, for an empty interval, `⊥`.

## Inputs
* `i` – interval lower bound
* `j` – interval upper bound
* `φ` – left formula
* `ψ` – right formula

## Hypotheses
* `hφ` – the left formula rewrites to sampled time
* `hψ` – the right formula rewrites to sampled time
* `hrec` – smaller untils rewrite to sampled time

## Conclusion
* the until rewrites to sampled time

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
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

theorem STL.Nnf.hasSampledRewrite_until (i j : ℕ) {φ ψ : STL.Nnf X} (hφ : φ.HasSampledRewrite)
    (hψ : ψ.HasSampledRewrite)
    (hrec : ∀ j' < j, ∀ i', (STL.Nnf.until i' j' φ ψ).HasSampledRewrite) : -- --- CONCL ---
    (STL.Nnf.until i j φ ψ).HasSampledRewrite := by -- --- PROOF ---
  obtain ⟨⟨sTφ, hTφ⟩, ⟨sFφ, hFφ⟩, ⟨sGφ, hGφ⟩⟩ := hφ
  obtain ⟨⟨sTψ, hTψ⟩, ⟨sFψ, hFψ⟩, ⟨sGψ, hGψ⟩⟩ := hψ
  by_cases hji : j < i
  · -- an empty interval: `⊥` implies everything
    have hbot : ∀ ξ, ¬ ((STL.Samp.lit (Pform.bot : Pform X)).toFormula 1).Satisfies ξ :=
      fun ξ h => (h : False)
    exact ⟨⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩,
      ⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩,
      ⟨.lit Pform.bot, fun ξ h => absurd h (hbot ξ)⟩⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `φ U[0,0] ψ ≡ ψ`, in each context
    obtain rfl : i = 0 := by omega
    have e : ∀ ξ : ℝ≥0 → X, (STL.Nnf.until 0 0 φ ψ).toFormula.Satisfies ξ ↔ ψ.toFormula.Satisfies ξ
        := by
      intro ξ
      simpa only [STL.Nnf.toFormula, Nat.cast_zero] using
        STL.until_zero_equiv φ.toFormula ψ.toFormula ξ
    refine ⟨⟨sTψ, fun ξ h => (e ξ).2 (hTψ ξ h)⟩, ⟨sFψ, fun ξ h => ?_⟩, ⟨sGψ, fun ξ h => ?_⟩⟩
    · obtain ⟨t, h₀, h₁, ht⟩ := hFψ ξ h
      exact ⟨t, h₀, h₁, (e _).2 ht⟩
    · exact fun t h₀ h₁ => (e _).2 (hGψ ξ h t h₀ h₁)
  -- a smaller bound, for the next step
  by_cases hi : i = 0
  · subst hi
    obtain ⟨⟨sT, hT⟩, ⟨sF, hF⟩, ⟨sG, hG⟩⟩ := hrec (j - 1) (by omega) 0
    simp only [STL.Nnf.toFormula, Nat.cast_zero] at hT hF hG
    refine ⟨⟨.or sTψ (.and sTφ (.and sGφ (.or sFψ (.next sT)))), fun ξ h => ?_⟩,
      ⟨.or sFψ (.and sGφ (.next (.or sTψ (.and sTφ (.and sGφ sF))))), fun ξ h => ?_⟩,
      ⟨.or sGψ (.and sGφ (.next (.or sTψ (.and sTφ (.and sGφ sG))))), fun ξ h => ?_⟩⟩
    · -- row `U[0,j]`
      have := STL.rewrite_until_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_or]
        at h ⊢
      rcases h with h | ⟨h₁, h₂, h₃ | h₃⟩
      · exact Or.inl (hTψ ξ h)
      · exact Or.inr ⟨hTφ ξ h₁, hGφ ξ h₂, Or.inl (hFψ ξ h₃)⟩
      · exact Or.inr ⟨hTφ ξ h₁, hGφ ξ h₂, Or.inr (hT _ h₃)⟩
    · -- row `F_I` of `U[0,j]`
      have := STL.rewrite_finOpen_until_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_or]
        at h ⊢
      rcases h with h | ⟨h₁, h₂⟩
      · exact Or.inl (hFψ ξ h)
      · refine Or.inr ⟨hGφ ξ h₁, ?_⟩
        rcases h₂ with h₂ | ⟨h₂, h₃, h₄⟩
        · exact Or.inl (hTψ _ h₂)
        · exact Or.inr ⟨hTφ _ h₂, hGφ _ h₃, hF _ h₄⟩
    · -- row `G_I` of `U[0,j]`
      have := STL.rewrite_globOpen_until_zero φ.toFormula ψ.toFormula j hj ξ
      simp only [STL.Nnf.toFormula, Nat.cast_zero] at this ⊢
      refine this ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_or]
        at h ⊢
      rcases h with h | ⟨h₁, h₂⟩
      · exact Or.inl (hGψ ξ h)
      · refine Or.inr ⟨hGφ ξ h₁, ?_⟩
        rcases h₂ with h₂ | ⟨h₂, h₃, h₄⟩
        · exact Or.inl (hTψ _ h₂)
        · exact Or.inr ⟨hTφ _ h₂, hGφ _ h₃, hG _ h₄⟩
  · -- `i ≥ 1`
    obtain ⟨⟨sT, hT⟩, ⟨sF, hF⟩, ⟨sG, hG⟩⟩ := hrec (j - 1) (by omega) (i - 1)
    have hi1 : 1 ≤ i := by omega
    have hij : i ≤ j := by omega
    refine ⟨⟨.and sTφ (.and sGφ (.next sT)), fun ξ h => ?_⟩,
      ⟨.and sGφ (.next (.and sTφ (.and sGφ sF))), fun ξ h => ?_⟩,
      ⟨.and sGφ (.next (.and sTφ (.and sGφ sG))), fun ξ h => ?_⟩⟩
    · -- row `U[i,j]`
      refine STL.rewrite_until_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next] at h ⊢
      exact ⟨hTφ ξ h.1, hGφ ξ h.2.1, hT _ h.2.2⟩
    · -- row `F_I` of `U[i,j]`
      refine STL.rewrite_finOpen_until_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next] at h ⊢
      exact ⟨hGφ ξ h.1, hTφ _ h.2.1, hGφ _ h.2.2.1, hF _ h.2.2.2⟩
    · -- row `G_I` of `U[i,j]`
      refine STL.rewrite_globOpen_until_succ φ.toFormula ψ.toFormula i j hi1 hij ξ ?_
      simp only [STL.Samp.toFormula, STL.Formula.sat_and, STL.Formula.sat_next] at h ⊢
      exact ⟨hGφ ξ h.1, hTφ _ h.2.1, hGφ _ h.2.2.1, hG _ h.2.2.2⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
