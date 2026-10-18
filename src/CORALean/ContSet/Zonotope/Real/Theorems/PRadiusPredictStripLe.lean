module

public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The P-radius after one prediction and one strip

[1, Eq. 4], at a single output and a known `A`: the estimate `X̂_k` is the prediction
`A X̂_{k-1} ⊕ F Bⁿʷ` met with the strip `|c₁ᵀ x - y| ≤ φ₁` at the gain `λ₁` [1, Eq. 3]. If the
quadratic form of [1, Eq. 8] is nonpositive,
`‖κ₁ A θ + κ₁ F γ + φ₁ λ₁ η‖²_P ≤ β ‖θ‖²_P + ‖F γ‖²₂ + φ₁² η²` for all `θ, γ, η`
(`κ₁ = I - λ₁ c₁ᵀ`), then the P-radius condition of [1, Eq. 4] holds,
`L_k ≤ β L_{k-1} + ψ + φ₁²`, in the form [1, Eq. 5] gives it: maximised over the coefficients.

The chain of [1, Eq. 5], [1, Eq. 6] and [1, Eq. 7] is the proof. A point of `X̂_k` is
`p̂_k + κ₁ A θ + κ₁ F γ + φ₁ λ₁ η` with `p̂_{k-1} + θ ∈ X̂_{k-1}`, `γ ∈ Bⁿʷ`, `η ∈ [-1, 1]`;
Eq. 8 bounds its squared P-distance by `β ‖θ‖²_P + ‖F γ‖² + φ₁² η²`, and that by
`β L_{k-1} + ψ + φ₁²` (`η² ≤ 1` is Eq. 7's added term `φ₁²(1 - η²) ≥ 0`). `L_{k-1}` and `ψ` are
any bounds of the P-radius and of `max_γ ‖F γ‖²`, the paper's being the least ones, and
`β ≥ 0`. The paper's display of `Ĥ_k(λ₁) ẑ` writes `F γ` for `κ₁ F γ`; its `A₁₂` and `A₂₂`, and
Eq. 3, have `κ₁ F`, which is what is used here.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.pRadius_predict_strip_le (A P : Mat ℝ n n) (F : Mat ℝ n m) (c l : Vec ℝ n)
    (φ y β L ψ : ℝ) (X : Zonotope (Vec ℝ n))
    (hJ : ∀ (θ : Vec ℝ n) (γ : Vec ℝ m) (η : ℝ),
      let κ : Mat ℝ n n := 1 - vecMulVec l c
      let e := κ *ᵥ (A *ᵥ θ) + κ *ᵥ (F *ᵥ γ) + (φ * η) • l
      e ⬝ᵥ (P *ᵥ e) ≤ β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + φ ^ 2 * η ^ 2)
    (hβ : 0 ≤ β) (hL : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c)) ≤ L)
    (hψ : ∀ γ : Vec ℝ m, (∀ j, |γ j| ≤ 1) → (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) ≤ ψ) : -- --- STMT ---
    let W : Zonotope (Vec ℝ n) := ⟨m, 0, fun j i => F i j⟩
    let Xk := ((X.mtimes A).plus W).intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n)
      (fun _ => φ) (fun _ => y) (Matrix.of fun r _ => l r : Mat ℝ n 1)
    Zonotope.pRadius P Xk ≤ β * L + ψ + φ ^ 2 := by -- --- PROOF ---
  intro W Xk
  refine csSup_le ⟨_, Xk.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∃ b : Fin (X.h + m + 1) → ℝ, (∀ j, |b j| ≤ 1) ∧
      z = Xk.c + ∑ j : Fin (X.h + m + 1), b j • Xk.G j := hz
  obtain ⟨b, hb, rfl⟩ := hz'
  -- the coefficients of `X̂_{k-1}`, of `W` and of the strip
  set β₁ : Fin X.h → ℝ := fun j => b (Fin.castAdd 1 (Fin.castAdd m j))
  set γ : Vec ℝ m := fun j => b (Fin.castAdd 1 (Fin.natAdd X.h j))
  set η : ℝ := b (Fin.natAdd (X.h + m) 0)
  set θ : Vec ℝ n := ∑ j, β₁ j • X.G j
  have hκ : (1 : Mat ℝ n n) - (Matrix.of fun r (_ : Fin 1) => l r) * (Matrix.of fun _ => c)
      = 1 - vecMulVec l c := by
    congr 1; ext i j; simp [Matrix.mul_apply, vecMulVec]
  -- the three generator blocks, each summed to its term of `κ A θ + κ F γ + φ λ η`
  have h1 : ∑ j : Fin X.h, β₁ j • ((1 - vecMulVec l c) *ᵥ (A *ᵥ X.G j)) =
      (1 - vecMulVec l c) *ᵥ (A *ᵥ θ) := by
    simp only [θ, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have h2 : ∑ j : Fin m, γ j • ((1 - vecMulVec l c) *ᵥ fun i => F i j) =
      (1 - vecMulVec l c) *ᵥ (F *ᵥ γ) := by
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h3 : ∑ j : Fin 1, b (Fin.natAdd (X.h + m) j) •
      ((Matrix.of fun r (_ : Fin 1) => l r) *ᵥ Pi.single j φ) = (φ * η) • l := by
    rw [Fin.sum_univ_one]
    ext i
    simp [η]
    ring
  simp only [β₁, γ] at h1 h2
  -- the point's offset from the new center is that sum
  beta_reduce
  rw [add_sub_cancel_left, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Xk, W, Zonotope.intersectStrip, Zonotope.plus, Zonotope.mtimes, Fin.append_left,
    Fin.append_right, hκ]
  rw [h1, h2, h3]
  -- Eq. 8, then the bounds of Eq. 6/7
  have hθ : θ ⬝ᵥ (P *ᵥ θ) ≤ L := by
    have := hL (X.c + θ) ⟨β₁, fun j => hb _, rfl⟩
    rwa [add_sub_cancel_left] at this
  have hγ : (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) ≤ ψ := hψ γ fun j => hb _
  have hη : η ^ 2 ≤ 1 := by
    have := hb (Fin.natAdd (X.h + m) 0)
    nlinarith [abs_nonneg η, sq_abs η, abs_le.mp this]
  calc _ ≤ β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + φ ^ 2 * η ^ 2 := hJ θ γ η
    _ ≤ β * L + ψ + φ ^ 2 * 1 := by
        gcongr
    _ = β * L + ψ + φ ^ 2 := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
