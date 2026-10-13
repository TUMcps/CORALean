import CORALean.ContSet.Zonotope.Real.Operations.CubMapMixed
import CORALean.ContSet.PolyZonotope.Real.Operations.CubEvalMixed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The coefficients of `Zonotope.cubMapMixed`

The three arguments of the mixed cubic map `(x₁ᵀ T x₂) * x₃` are points `xₛ = Σ βₛ [cₛ,Gₛ]` of
three independent zonotopes, so the image is the trilinear polynomial
`Σⱼ Σᵦ Σₐ β₃ⱼ β₂ᵦ β₁ₐ t(a, b, j)` in the extended factors `(1, p)` of each, one generator per
triple. Each product is in `[-1, 1]`, which is the only place the enclosure is lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The trilinear expansion of the mixed cubic map over the three families of extended columns. -/
theorem Zonotope.aux_cubMapMixed_expand (T : Fin m → Fin n → Mat ℝ n n) {N₁ N₂ N₃ : ℕ}
    (β₁ : Fin N₁ → ℝ) (β₂ : Fin N₂ → ℝ) (β₃ : Fin N₃ → ℝ) (u₁ : Fin N₁ → Vec ℝ n)
    (u₂ : Fin N₂ → Vec ℝ n) (u₃ : Fin N₃ → Vec ℝ n) (i : Fin m) :
    PolyZonotope.cubEvalMixed T (∑ a, β₁ a • u₁ a) (∑ b, β₂ b • u₂ b) (∑ j, β₃ j • u₃ j) i
      = ∑ j, ∑ b, ∑ a, β₃ j * β₂ b * β₁ a * ∑ k, (u₁ a ⬝ᵥ (T i k *ᵥ u₂ b)) * u₃ j k
    := by -- --- PROOF ---
  unfold PolyZonotope.cubEvalMixed
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_dotProduct, mulVec_sum,
    dotProduct_sum, smul_dotProduct, mulVec_smul, dotProduct_smul, mul_assoc]
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- the outermost sum over `k` moves innermost and the one over `j` outermost
  have e : ∀ f : Fin n → Fin N₂ → Fin N₁ → Fin N₃ → ℝ,
      ∑ k, ∑ b, ∑ a, ∑ j, f k b a j = ∑ j, ∑ b, ∑ a, ∑ k, f k b a j := fun f => by
    calc ∑ k, ∑ b, ∑ a, ∑ j, f k b a j
        = ∑ k, ∑ b, ∑ j, ∑ a, f k b a j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ b, ∑ a, f k b a j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ b, ∑ a, f k b a j := Finset.sum_comm
      _ = ∑ j, ∑ b, ∑ k, ∑ a, f k b a j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ j, ∑ b, ∑ a, ∑ k, f k b a j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

/-- With every extended factor `1` at index `0`, the `((0, 0), 0)` term is the centre. -/
theorem Zonotope.aux_cubMapMixed_centre {h₁ h₂ h₃ : ℕ} (β₁ : Fin (h₁ + 1) → ℝ)
    (β₂ : Fin (h₂ + 1) → ℝ) (β₃ : Fin (h₃ + 1) → ℝ) (e₁ : β₁ 0 = 1) (e₂ : β₂ 0 = 1)
    (e₃ : β₃ 0 = 1) (Q : Fin (h₃ + 1) → Fin (h₂ + 1) → Fin (h₁ + 1) → ℝ) :
    ∑ j, ∑ b, ∑ a, β₃ j * β₂ b * β₁ a * Q j b a
      = Q 0 0 0 + ∑ j, ∑ b, ∑ a,
          β₃ j * β₂ b * β₁ a * (if j = 0 ∧ b = 0 ∧ a = 0 then 0 else Q j b a) := by -- --- PROOF ---
  -- the `((0, 0), 0)` term split off, pointwise
  have key : ∀ j b a, β₃ j * β₂ b * β₁ a * Q j b a
      = (if j = 0 ∧ b = 0 ∧ a = 0 then Q 0 0 0 else 0)
        + β₃ j * β₂ b * β₁ a * (if j = 0 ∧ b = 0 ∧ a = 0 then 0 else Q j b a) :=
    fun j b a => by
    by_cases h : j = 0 ∧ b = 0 ∧ a = 0
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [e₁, e₂, e₃]
    · simp [h]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => key j b a]
  simp only [Finset.sum_add_distrib]
  -- the first sum is the single term at `0`
  have h0 : ∑ j : Fin (h₃ + 1), ∑ b : Fin (h₂ + 1), ∑ a : Fin (h₁ + 1),
      (if j = 0 ∧ b = 0 ∧ a = 0 then Q 0 0 0 else 0) = Q 0 0 0 := by
    simp [ite_and]
  rw [h0]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cubic image of the point `(x₁, x₂, x₃)` is the centre plus the generators of `cubMapMixed`
at the products `β₃ⱼ β₂ᵦ β₁ₐ` of the extended factors, those of the linear generators of each
family being that family's `p`. -/
theorem Zonotope.cubMapMixed_coeff (T : Fin m → Fin n → Mat ℝ n n)
    (Z₁ Z₂ Z₃ : Zonotope (Vec ℝ n)) (p₁ : Fin Z₁.h → ℝ) (p₂ : Fin Z₂.h → ℝ)
    (p₃ : Fin Z₃.h → ℝ) (hp₁ : ∀ j, |p₁ j| ≤ 1) (hp₂ : ∀ j, |p₂ j| ≤ 1)
    (hp₃ : ∀ j, |p₃ j| ≤ 1) :
    ∃ γ : Fin (Z₁.cubMapMixed T Z₂ Z₃).h → ℝ, (∀ l, |γ l| ≤ 1)
      ∧ (∀ a : Fin Z₁.h,
          γ ((Zonotope.cubIdx (Z₃.h + 1) (Z₂.h + 1) (Z₁.h + 1)).symm ((0, 0), a.succ)) = p₁ a)
      ∧ (∀ b : Fin Z₂.h,
          γ ((Zonotope.cubIdx (Z₃.h + 1) (Z₂.h + 1) (Z₁.h + 1)).symm ((0, b.succ), 0)) = p₂ b)
      ∧ (∀ j : Fin Z₃.h,
          γ ((Zonotope.cubIdx (Z₃.h + 1) (Z₂.h + 1) (Z₁.h + 1)).symm ((j.succ, 0), 0)) = p₃ j)
      ∧ PolyZonotope.cubEvalMixed T (Z₁.c + ∑ j, p₁ j • Z₁.G j) (Z₂.c + ∑ j, p₂ j • Z₂.G j)
          (Z₃.c + ∑ j, p₃ j • Z₃.G j)
        = (Z₁.cubMapMixed T Z₂ Z₃).c + ∑ l, γ l • (Z₁.cubMapMixed T Z₂ Z₃).G l
    := by -- --- PROOF ---
  -- the extended columns `[c, G]` and factors `(1, p)` of each set
  obtain ⟨u₁, hu₁⟩ : ∃ u : Fin (Z₁.h + 1) → Vec ℝ n, u = Fin.cons Z₁.c Z₁.G := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : Fin (Z₂.h + 1) → Vec ℝ n, u = Fin.cons Z₂.c Z₂.G := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃⟩ : ∃ u : Fin (Z₃.h + 1) → Vec ℝ n, u = Fin.cons Z₃.c Z₃.G := ⟨_, rfl⟩
  set idx := Zonotope.cubIdx (Z₃.h + 1) (Z₂.h + 1) (Z₁.h + 1) with hidx
  set β₁ : Fin (Z₁.h + 1) → ℝ := Fin.cons 1 p₁ with hβ₁
  set β₂ : Fin (Z₂.h + 1) → ℝ := Fin.cons 1 p₂ with hβ₂
  set β₃ : Fin (Z₃.h + 1) → ℝ := Fin.cons 1 p₃ with hβ₃
  -- every extended factor lies in `[-1, 1]`
  have hb : ∀ {h : ℕ} (p : Fin h → ℝ), (∀ j, |p j| ≤ 1) →
      ∀ a, |(Fin.cons 1 p : Fin (h + 1) → ℝ) a| ≤ 1 := fun p hp a => by
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simpa using hp j
  -- the coefficient of generator `((j, b), a)` is `β₃ⱼ β₂ᵦ β₁ₐ`
  refine ⟨fun l => β₃ (idx l).1.1 * β₂ (idx l).1.2 * β₁ (idx l).2, fun l => ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [abs_mul, abs_mul]
    exact mul_le_one₀ (mul_le_one₀ (hb p₃ hp₃ _) (abs_nonneg _) (hb p₂ hp₂ _))
      (abs_nonneg _) (hb p₁ hp₁ _)
  -- the linear generators of the three families carry the `p`s
  · intro a
    simp [hβ₁, hβ₂, hβ₃, hidx]
  · intro b
    simp [hβ₁, hβ₂, hβ₃, hidx]
  · intro j
    simp [hβ₁, hβ₂, hβ₃, hidx]
  -- the point, coordinate by coordinate
  · funext i
    have hx : ∀ {h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n) (p : Fin h → ℝ)
        (u : Fin (h + 1) → Vec ℝ n), u = Fin.cons c G →
        c + ∑ j, p j • G j = ∑ a, (Fin.cons 1 p : Fin (h + 1) → ℝ) a • u a :=
      fun c G p u hu => by rw [hu, Fin.sum_univ_succ]; simp
    show PolyZonotope.cubEvalMixed T (Z₁.c + ∑ j, p₁ j • Z₁.G j) (Z₂.c + ∑ j, p₂ j • Z₂.G j)
        (Z₃.c + ∑ j, p₃ j • Z₃.G j) i = _
    rw [hx Z₁.c Z₁.G p₁ u₁ hu₁, hx Z₂.c Z₂.G p₂ u₂ hu₂, hx Z₃.c Z₃.G p₃ u₃ hu₃,
      Zonotope.aux_cubMapMixed_expand]
    -- the generators of `cubMapMixed`, a sum over the ordered triples
    rw [Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    symm
    refine (congrArg₂ _ rfl ((Fintype.sum_equiv idx _
      (fun t : (Fin (Z₃.h + 1) × Fin (Z₂.h + 1)) × Fin (Z₁.h + 1) =>
        β₃ t.1.1 * β₂ t.1.2 * β₁ t.2 *
          (if t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0 then 0 else
            ∑ k, (u₁ t.2 ⬝ᵥ (T i k *ᵥ u₂ t.1.2)) * u₃ t.1.1 k))
      fun l => by subst hu₁ hu₂ hu₃; rfl))).trans ?_
    simp only [Fintype.sum_prod_type]
    -- the centre is the `((0, 0), 0)` entry, the generators the rest
    have hc : (Z₁.cubMapMixed T Z₂ Z₃).c i = ∑ k, (u₁ 0 ⬝ᵥ (T i k *ᵥ u₂ 0)) * u₃ 0 k := by
      subst hu₁ hu₂ hu₃; rfl
    rw [hc]
    exact (Zonotope.aux_cubMapMixed_centre β₁ β₂ β₃ rfl rfl rfl
      (fun j b a => ∑ k, (u₁ a ⬝ᵥ (T i k *ᵥ u₂ b)) * u₃ j k)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
