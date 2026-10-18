module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Theorems.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Float.Theorems.PowOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.compose` encloses `g ∘ f`

As at the exact layer, for any real coefficients `a k` inside the stored enclosures.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.compose_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (g : ℝ → ℝ)
    (c : 𝕋) (lo hi : ℕ → 𝕋) (N : ℕ) (ρ : 𝕋) (a : ℕ → ℝ)
    (ha : ∀ k ≤ N, toReal (lo k) ≤ a k ∧ a k ≤ toReal (hi k))
    (hg : ∀ t ∈ Real.Taylm.box n,
      |g (f t) - ∑ k ∈ Finset.range (N + 1), a k * (f t - toReal c) ^ k| ≤ toReal ρ) :
    (T.compose c lo hi N ρ).Encloses fun t => g (f t) := by -- --- PROOF ---
  have hc := Taylm.minus_outer h (Taylm.const_outer (n := n) c T.maxOrder)
  have hs := Taylm.sum_outer (T := fun k : Fin (N + 1) =>
    ((T.minus (Taylm.const n c T.maxOrder)).pow k).smul (lo k) (hi k))
    (f := fun k t => a k * (f t - toReal c) ^ (k : ℕ))
    fun k => Taylm.smul_outer (ha k (Nat.lt_succ_iff.1 k.isLt)) (Taylm.pow_outer hc k)
  intro t ht
  have h₁ := hs t ht
  have h₂ := abs_le.1 (hg t ht)
  rw [Finset.sum_range (fun k => a k * (f t - toReal c) ^ k)] at h₂
  -- the sum's remainder and box, each widened by the Lagrange term's and the empty box
  set S := Taylm.sum fun k : Fin (N + 1) =>
    ((T.minus (Taylm.const n c T.maxOrder)).pow k).smul (lo k) (hi k) with hS
  have := addDown_le_add S.rem.inf (neg ρ)
  have := add_le_addUp S.rem.sup ρ
  have := addDown_le_add S.I_error.inf zero
  have := add_le_addUp S.I_error.sup zero
  simp only [Taylm.compose, Taylm.plus, Taylm.inflated, Real.Taylm.poly, List.map_append,
    Real.Taylm.polyOf_append, List.map_nil, Real.Taylm.polyOf_nil, toReal_neg, toReal_zero,
    add_zero] at *
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
