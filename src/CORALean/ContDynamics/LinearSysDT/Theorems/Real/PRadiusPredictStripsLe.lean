module

public import CORALean.ContDynamics.Conform.Theorems.UnrollAffine
public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.ContSet.ContSet.Operations.IntersectStripSeq
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD
public import CORALean.ContSet.Zonotope.Real.Theorems.PredictDev

@[expose] public section

/-!
# The P-radius after one prediction and `p` strips

[1, Eq. 4] at several outputs, [1, Alg. 2]: the estimate is the prediction met with the strips
of the outputs one after another at the offline gains `λₛ`, the columns of `Λ`. If the quadratic
form of `Ĥ_{k/p} ẑ` is bounded, `‖(κ_{p-1} ⋯ κ₀)(A θ + F γ) + ∑ₛ ηₛ (κ_{p-1} ⋯ κₛ₊₁) uₛ‖²_P ≤
β ‖θ‖²_P + ‖F γ‖² + ∑ₛ φₛ² ηₛ²` for all `θ, γ, η` (`κₛ = I - λₛ cₛᵀ`, `uₛ = φₛ λₛ`), then
`L_k ≤ β L_{k-1} + ψ + φ₀² + … + φ_{p-1}²`. A point of the estimate is, by `aux_intersectStrip_dev`
strip after strip, `κ` of a point of the zonotope before plus `φ η λ`; unrolled, that is the
product form above.

## Inputs
* `A` – state matrix
* `P` – radius matrix
* `F` – disturbance matrix
* `C` – output matrix
* `φ` – strip widths
* `y` – measurements
* `Λ` – gain columns
* `κ` – strip update matrices
* `u` – gain direction vectors
* `β` – contraction factor
* `L` – bound on the previous radius
* `ψ` – bound on the disturbance term
* `X` – previous zonotope

## Hypotheses
* `hκ` – update matrices built from the gains
* `hu` – direction vectors built from gains and widths
* `hJ` – the quadratic form bound holds
* `hβ` – contraction factor nonnegative
* `hL` – previous radius bounded by `L`
* `hψ` – disturbance term bounded by `ψ`

## Conclusion
* the P-radius after the prediction and strips is at most the stated bound

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n m : ℕ}


end


section
variable {n : ℕ}

/-- A point of the strip intersection is `κ` of a point before it plus `φ η λ`. -/
theorem Zonotope.aux_intersectStrip_dev (c l : Vec ℝ n) (φ y : ℝ) (Z : Zonotope (Vec ℝ n))
    {z : Vec ℝ n}
    (hz : z ∈ (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
      (Matrix.of fun r _ => l r : Mat ℝ n 1)).construct) : -- --- CONCL ---
    ∃ z₁ ∈ Z.construct, ∃ η : ℝ, |η| ≤ 1 ∧
      z - (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
        (Matrix.of fun r _ => l r : Mat ℝ n 1)).c
        = (1 - vecMulVec l c) *ᵥ (z₁ - Z.c) + (φ * η) • l := by -- --- PROOF ---
  obtain ⟨b, hb, rfl⟩ := hz
  -- the coefficients of the zonotope before, and of the strip's own generator
  refine ⟨Z.c + ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • Z.G j, ⟨_, fun j => hb _, rfl⟩,
    b (Fin.natAdd Z.h 0), hb _, ?_⟩
  have hκ : (1 : Mat ℝ n n) - (Matrix.of fun r (_ : Fin 1) => l r) * (Matrix.of fun _ => c)
      = 1 - vecMulVec l c := by
    congr 1; ext i j; simp [Matrix.mul_apply, vecMulVec]
  -- the generators of the old zonotope sum to `κ` of the old deviation
  have h1 : ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • ((1 - vecMulVec l c) *ᵥ Z.G j) =
      (1 - vecMulVec l c) *ᵥ ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • Z.G j := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  have h3 : ∑ j : Fin 1, b (Fin.natAdd Z.h j) •
      ((Matrix.of fun r (_ : Fin 1) => l r) *ᵥ Pi.single j φ) = (φ * b (Fin.natAdd Z.h 0)) • l := by
    rw [Fin.sum_univ_one]
    ext i
    simp
    ring
  rw [add_sub_cancel_left, add_sub_cancel_left, ← h1, ← h3]
  erw [Fin.sum_univ_add]
  simp only [Zonotope.intersectStrip, Fin.append_left, Fin.append_right, hκ]

end


/-- The deviation after `s` strips: each applies `κₛ` and adds `ηₛ uₛ`. -/
def aux_stripDev (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n) (η : ℕ → ℝ) : ℕ → Vec ℝ n → Vec ℝ n
  | 0, d => d
  | s + 1, d => κ s *ᵥ aux_stripDev κ u η s d + η s • u s

/-- The first `s` strips of the sequence, met one after another. -/
def aux_stripsUpTo (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p) (Z : Zonotope (Vec ℝ n))
    (s : ℕ) : Zonotope (Vec ℝ n) :=
  ((List.finRange p).take s).foldl
    (fun X i => X.intersectStrip (Matrix.of fun _ => C i : Mat ℝ 1 n) (fun _ => φ i)
      (fun _ => y i) (Matrix.of fun r _ => Λ r i : Mat ℝ n 1)) Z

/-- The deviation of a strip chain depends only on the coefficients it uses. -/
theorem aux_stripDev_congr (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n) (η η' : ℕ → ℝ) (d : Vec ℝ n)
    (s : ℕ) (h : ∀ r < s, η r = η' r) : -- --- CONCL ---
    aux_stripDev κ u η s d = aux_stripDev κ u η' s d := by -- --- PROOF ---
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [aux_stripDev]
    rw [ih fun r hr => h r (by omega), h s (by omega)]

/-- The deviation of a strip chain is the product form of the recursion. -/
theorem aux_stripDev_eq (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n) (η : ℕ → ℝ) (d : Vec ℝ n)
    (s : ℕ) : -- --- CONCL ---
    aux_stripDev κ u η s d = Conform.prodJac κ s s *ᵥ d
      + ∑ i ∈ Finset.range s, η i • (Conform.prodJac κ s (s - i - 1) *ᵥ u i) := by -- --- PROOF ---
  have h := Conform.unroll_affine κ (fun s => aux_stripDev κ u η s d) (fun s => η s • u s)
    (fun s => rfl) s
  simp only [aux_stripDev] at h
  rw [h]
  simp only [mulVec_smul]

/-- The first `s + 1` strips are the first `s` and then strip `s`. -/
theorem aux_stripsUpTo_succ (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (Z : Zonotope (Vec ℝ n)) (s : ℕ) (hs : s < p) : -- --- CONCL ---
    aux_stripsUpTo C φ y Λ Z (s + 1)
      = (aux_stripsUpTo C φ y Λ Z s).intersectStrip (Matrix.of fun _ => C ⟨s, hs⟩ : Mat ℝ 1 n)
        (fun _ => φ ⟨s, hs⟩) (fun _ => y ⟨s, hs⟩)
        (Matrix.of fun r _ => Λ r ⟨s, hs⟩ : Mat ℝ n 1) := by -- --- PROOF ---
  unfold aux_stripsUpTo
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem (by simpa using hs : s < (List.finRange p).length)]

/-- The strips of `intersectStripSeq` at constant gains are the `p` strips of the chain. -/
theorem aux_stripsUpTo_full (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (Z : Zonotope (Vec ℝ n)) :
    aux_stripsUpTo C φ y Λ Z p = ContSet.intersectStripSeq (S := 𝒵) C φ y (fun _ => Λ) Z := by
  unfold aux_stripsUpTo ContSet.intersectStripSeq
  rw [List.take_of_length_le (by simp)]
  rfl

/-- A point after `s` strips is the deviation chain of a point of the zonotope before them. -/
theorem aux_stripsUpTo_dev (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n)
    (hκ : ∀ s : Fin p, κ s = 1 - vecMulVec (fun r => Λ r s) (C s))
    (hu : ∀ s : Fin p, u s = φ s • fun r => Λ r s) (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    ∀ s ≤ p, ∀ z ∈ (aux_stripsUpTo C φ y Λ Z s).construct, ∃ z₀ ∈ Z.construct, ∃ η : ℕ → ℝ,
      (∀ r, |η r| ≤ 1) ∧
        z - (aux_stripsUpTo C φ y Λ Z s).c = aux_stripDev κ u η s (z₀ - Z.c) := by -- --- PROOF ---
  intro s
  induction s with
  | zero =>
    intro _ z hz
    exact ⟨z, hz, fun _ => 0, fun _ => by simp, rfl⟩
  | succ s ih =>
    intro hsp z hz
    have hs : s < p := hsp
    rw [aux_stripsUpTo_succ C φ y Λ Z s hs] at hz ⊢
    obtain ⟨z₁, hz₁, ηs, hηs, hdev⟩ := Zonotope.aux_intersectStrip_dev _ _ _ _ _ hz
    obtain ⟨z₀, hz₀, η', hη', hdev'⟩ := ih (by omega) z₁ hz₁
    -- the new coefficient joins the old ones at position `s`
    refine ⟨z₀, hz₀, fun r => if r = s then ηs else η' r, fun r => ?_, ?_⟩
    · by_cases hr : r = s <;> simp [hr, hηs, hη' r]
    · have hk := hκ ⟨s, hs⟩
      have hv := hu ⟨s, hs⟩
      rw [hdev, hdev', aux_stripDev, hk, hv, aux_stripDev_congr κ u (fun r => if r = s then ηs
        else η' r) η' _ s (fun r hr => by simp [Nat.ne_of_lt hr])]
      simp only [if_true, smul_smul]
      rw [mul_comm ηs]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: the quadratic form of `Ĥ_{k/p} ẑ` bounds the P-radius after `p` strips. -/
theorem Zonotope.pRadius_predict_strips_le (A P : Mat ℝ n n) (F : Mat ℝ n m) (C : Mat ℝ p n)
    (φ y : Vec ℝ p) (Λ : Mat ℝ n p) (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n)
    (hκ : ∀ s : Fin p, κ s = 1 - vecMulVec (fun r => Λ r s) (C s))
    (hu : ∀ s : Fin p, u s = φ s • fun r => Λ r s) (β L ψ : ℝ) (X : Zonotope (Vec ℝ n))
    (hJ : ∀ (θ : Vec ℝ n) (γ : Vec ℝ m) (η : Fin p → ℝ),
      let e := Conform.prodJac κ p p *ᵥ (A *ᵥ θ + F *ᵥ γ)
        + ∑ s : Fin p, η s • (Conform.prodJac κ p (p - s - 1) *ᵥ u s)
      e ⬝ᵥ (P *ᵥ e) ≤ β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ)
        + ∑ s : Fin p, φ s ^ 2 * η s ^ 2)
    (hβ : 0 ≤ β) (hL : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c)) ≤ L)
    (hψ : ∀ γ : Vec ℝ m, (∀ j, |γ j| ≤ 1) → (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) ≤ ψ) : -- --- CONCL ---
    Zonotope.pRadius P (ContSet.intersectStripSeq (S := 𝒵) C φ y (fun _ => Λ)
        ((X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Zonotope (Vec ℝ n))))
      ≤ β * L + ψ + ∑ s : Fin p, φ s ^ 2 := by -- --- PROOF ---
  set X' := (X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Zonotope (Vec ℝ n)) with hX'
  set Xk := ContSet.intersectStripSeq (S := 𝒵) C φ y (fun _ => Λ) X' with hXk
  refine csSup_le ⟨_, Xk.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  -- the point is a deviation chain over a prediction point
  have hc : Xk = aux_stripsUpTo C φ y Λ X' p := (aux_stripsUpTo_full C φ y Λ X').symm
  rw [hc] at hz ⊢
  obtain ⟨z₀, hz₀, η, hη, hdev⟩ := aux_stripsUpTo_dev C φ y Λ κ u hκ hu X' p le_rfl z hz
  obtain ⟨θ, γ, hθ, hγ, hz₀dev⟩ := Zonotope.predict_dev A F X hz₀
  show (z - (aux_stripsUpTo C φ y Λ X' p).c) ⬝ᵥ P *ᵥ (z - (aux_stripsUpTo C φ y Λ X' p).c) ≤ _
  rw [hdev, hz₀dev, aux_stripDev_eq, Finset.sum_range (fun i => η i • (Conform.prodJac κ p
    (p - i - 1) *ᵥ u i))]
  -- the bounds of the old estimate, the disturbance and the coefficients
  have hθL : θ ⬝ᵥ (P *ᵥ θ) ≤ L := by
    have := hL (X.c + θ) hθ
    rwa [add_sub_cancel_left] at this
  have hη2 : ∀ s : Fin p, η s ^ 2 ≤ 1 := fun s => by
    have := hη s
    nlinarith [abs_nonneg (η s), sq_abs (η s), abs_le.mp this]
  calc _ ≤ β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + ∑ s : Fin p, φ s ^ 2 * η s ^ 2 :=
        hJ θ γ fun s => η s
    _ ≤ β * L + ψ + ∑ s : Fin p, φ s ^ 2 := by
        gcongr with s
        · exact hψ γ hγ
        · nlinarith [hη2 s, sq_nonneg (φ s)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
