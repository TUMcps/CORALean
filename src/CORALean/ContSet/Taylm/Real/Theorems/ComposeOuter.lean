module

public import CORALean.ContSet.Taylm.Real.Operations.Compose
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PowOuter
public import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Real.Theorems.SumOuter

@[expose] public section

/-!
# `Taylm.compose` encloses `g ∘ f`

The model arithmetic alone: if `ρ` bounds how far `g ∘ f` is from the polynomial in
`f - c` on the box, the composed model encloses `g ∘ f`. Where `ρ` comes from is
`TaylorOuter`'s business.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.compose_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (g : ℝ → ℝ)
    (c : ℝ) (a : ℕ → ℝ) (N : ℕ) (ρ : ℝ)
    (hg : ∀ t ∈ Taylm.box n,
      |g (f t) - ∑ k ∈ Finset.range (N + 1), a k * (f t - c) ^ k| ≤ ρ) :
    (T.compose c a N ρ).Encloses fun t => g (f t) := by -- --- PROOF ---
  have hc := Taylm.minus_outer h (Taylm.const_outer (n := n) c T.maxOrder)
  -- the polynomial part encloses the polynomial in `f - c`
  have hs := Taylm.sum_outer (T := fun k : Fin (N + 1) =>
    ((T.minus (Taylm.const n c T.maxOrder)).pow k).smul (a k))
    (f := fun k t => a k * (f t - c) ^ (k : ℕ))
    fun k => Taylm.smul_outer (a k) (Taylm.pow_outer hc k)
  intro t ht
  have h₁ := hs t ht
  have h₂ := abs_le.1 (hg t ht)
  rw [Finset.sum_range (fun k => a k * (f t - c) ^ k)] at h₂
  simp only [Taylm.compose, Taylm.plus, Taylm.poly, Taylm.polyOf_append,
    Taylm.polyOf_nil] at *
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
