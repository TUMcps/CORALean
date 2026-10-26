module

public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.Operations.NthrootZFloat
public import CORALean.Specification.SyntaxTree.Theorems.NthrootFloatContains

@[expose] public section

/-!
# `nthrootZFloat` contains the root

An interval `SyntaxTree.nthrootZFloat` returns holds `nthrootZ` of the number it is given: the root
for a nonnegative degree (`nthrootFloat_contains`), and for a negative one the reciprocal of a root
certified to keep its sign, which reverses the order of the bounds and is rounded outward.

## Inputs
* `steps` – bisection steps
* `x` – number
* `e` – integer degree

## Hypotheses
* none

## Conclusion
* every returned interval contains the root of that degree
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SyntaxTree.nthrootZFloat_contains (steps : ℕ) (x : 𝕋) (e : ℤ) : -- --- CONCL ---
    ∀ J ∈ SyntaxTree.nthrootZFloat steps x e,
      toReal J.inf ≤ SyntaxTree.nthrootZ (toReal x) e ∧
        SyntaxTree.nthrootZ (toReal x) e ≤ toReal J.sup := by -- --- PROOF ---
  intro J hJ
  unfold SyntaxTree.nthrootZFloat at hJ
  unfold SyntaxTree.nthrootZ
  by_cases he : 0 ≤ e
  · -- a nonnegative degree: the root itself
    rw [if_pos he] at hJ ⊢
    obtain rfl := Option.some.inj hJ
    exact SyntaxTree.nthrootFloat_contains steps x e.toNat
  rw [if_neg he] at hJ ⊢
  dsimp only at hJ
  obtain ⟨hlo, hhi⟩ := SyntaxTree.nthrootFloat_contains steps x (-e).toNat
  generalize SyntaxTree.nthrootFloat steps x (-e).toNat = I at hJ hlo hhi
  generalize SyntaxTree.nthroot (toReal x) (-e).toNat = r at hlo hhi ⊢
  by_cases hp : ltStrict zero I.inf = true
  · -- a positive root: `[1/sup, 1/inf]`, rounded outward
    rw [if_pos hp] at hJ
    obtain rfl := Option.some.inj hJ
    have h0 := toReal_lt_of_ltStrict hp
    rw [toReal_zero] at h0
    have hs : 0 < toReal I.sup := lt_of_lt_of_le h0 (hlo.trans hhi)
    have hr : 0 < r := lt_of_lt_of_le h0 hlo
    have d1 := divDown_le_div one I.sup hs
    have d2 := div_le_divUp one I.inf h0
    rw [toReal_one, one_div] at d1 d2
    exact ⟨d1.trans (inv_anti₀ hr hhi), (inv_anti₀ h0 hlo).trans d2⟩
  -- not certified positive: a negative root, or none
  rw [if_neg hp] at hJ
  by_cases hn : ltStrict I.sup zero = true
  · -- a negative root: the same, reflected
    rw [if_pos hn] at hJ
    obtain rfl := Option.some.inj hJ
    have h0 := toReal_lt_of_ltStrict hn
    rw [toReal_zero] at h0
    have hi' : 0 < toReal (neg I.inf) := by rw [toReal_neg]; linarith [hlo.trans hhi]
    have hs' : 0 < toReal (neg I.sup) := by rw [toReal_neg]; linarith
    have hr : r < 0 := lt_of_le_of_lt hhi h0
    have d1 := div_le_divUp one (neg I.sup) hs'
    have d2 := divDown_le_div one (neg I.inf) hi'
    rw [toReal_one, one_div, toReal_neg] at d1 d2
    -- `1/x` falls on the negative reals, so the reciprocal bounds swap
    simp only [toReal_neg]
    constructor
    · have := inv_le_inv_of_neg h0 hr |>.2 hhi
      rw [inv_neg] at d1
      linarith
    · have := inv_le_inv_of_neg hr (lt_of_le_of_lt hlo (lt_of_le_of_lt hhi h0)) |>.2 hlo
      rw [inv_neg] at d2
      linarith
  · rw [if_neg hn] at hJ
    exact absurd hJ (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
