module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# A float constrained zonotope's nominal set, bounded at any dual weights

The coefficient program `max (Gᵀa)ᵀβ` over `|βⱼ| ≤ 1`, `β ∈ P` is bounded by weak
duality at *any* nonnegative weights `y, zu, zl` of `P`'s rows: with the residual
`r = Gᵀa - Aᵀy - Aeᵀzu + Aeᵀzl`,

  `(Gᵀa)ᵀβ = rᵀβ + yᵀ(Aβ) + zuᵀ(Aeβ) - zlᵀ(Aeβ) ≤ Σ |rⱼ| + yᵀb + zuᵀbe - zlᵀbe`,

the unit box paying for the residual, each right-hand side widened by its row's slack. Nothing asks
the weights to be optimal or the residual to vanish: `rⱼ` is enclosed in rounded arithmetic and
`|rⱼ|` bounded by the larger end, and every weight is clamped at zero, so even its sign is not
trusted. Sound for every weight vector; tight only for optimal ones.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A proposed weight, made admissible. -/
def ConZonotope.aux_clamp (w : 𝕋) : 𝕋 := maximum zero w

/-- An upper end of the residual's `j`-th entry. -/
def ConZonotope.aux_resUp (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (y : Vec 𝕋 cZ.P.m)
    (zu zl : Vec 𝕋 cZ.P.me) (j : Fin cZ.h) : 𝕋 :=
  addUp (dotUp a (cZ.G j))
    (addUp (neg (dotDown y fun k => cZ.P.A k j))
      (addUp (neg (dotDown zu fun k => cZ.P.Ae k j)) (dotUp zl fun k => cZ.P.Ae k j)))

/-- A lower end of the residual's `j`-th entry. -/
def ConZonotope.aux_resDown (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (y : Vec 𝕋 cZ.P.m)
    (zu zl : Vec 𝕋 cZ.P.me) (j : Fin cZ.h) : 𝕋 :=
  addDown (dotDown a (cZ.G j))
    (addDown (neg (dotUp y fun k => cZ.P.A k j))
      (addDown (neg (dotUp zu fun k => cZ.P.Ae k j)) (dotDown zl fun k => cZ.P.Ae k j)))

theorem ConZonotope.aux_clamp_nonneg (w : 𝕋) :
    0 ≤ toReal (ConZonotope.aux_clamp w) := by
  rw [ConZonotope.aux_clamp, toReal_maximum, toReal_zero]
  exact le_max_left _ _

/-- A weighted sum of rows applied to `β`, read column by column. -/
theorem ConZonotope.aux_sum_swap {p q : ℕ} (u : Fin p → ℝ) (M : Fin p → Fin q → ℝ)
    (β : Fin q → ℝ) :
    ∑ k, u k * ∑ j, M k j * β j = ∑ j, β j * ∑ k, u k * M k j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The upper and lower ends enclose the exact residual. -/
theorem ConZonotope.aux_res_encl (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (y : Vec 𝕋 cZ.P.m)
    (zu zl : Vec 𝕋 cZ.P.me) (j : Fin cZ.h) : -- --- STMT ---
    let r := (∑ i, toReal (a i) * toReal (cZ.G j i))
      - (∑ k, toReal (y k) * toReal (cZ.P.A k j))
      - (∑ k, toReal (zu k) * toReal (cZ.P.Ae k j))
      + ∑ k, toReal (zl k) * toReal (cZ.P.Ae k j)
    toReal (ConZonotope.aux_resDown cZ a y zu zl j) ≤ r
      ∧ r ≤ toReal (ConZonotope.aux_resUp cZ a y zu zl j) := by -- --- PROOF ---
  intro r
  -- each of the four products, enclosed by its rounded dot product
  have h1 := le_dotUp a (cZ.G j)
  have h2 := dotDown_le a (cZ.G j)
  have h3 := le_dotUp y fun k => cZ.P.A k j
  have h4 := dotDown_le y fun k => cZ.P.A k j
  have h5 := le_dotUp zu fun k => cZ.P.Ae k j
  have h6 := dotDown_le zu fun k => cZ.P.Ae k j
  have h7 := le_dotUp zl fun k => cZ.P.Ae k j
  have h8 := dotDown_le zl fun k => cZ.P.Ae k j
  refine ⟨?_, ?_⟩
  -- the lower end, its three additions rounded down
  · have e1 := addDown_le_add (neg (dotUp zu fun k => cZ.P.Ae k j))
      (dotDown zl fun k => cZ.P.Ae k j)
    have e2 := addDown_le_add (neg (dotUp y fun k => cZ.P.A k j))
      (addDown (neg (dotUp zu fun k => cZ.P.Ae k j)) (dotDown zl fun k => cZ.P.Ae k j))
    have e3 := addDown_le_add (dotDown a (cZ.G j))
      (addDown (neg (dotUp y fun k => cZ.P.A k j))
        (addDown (neg (dotUp zu fun k => cZ.P.Ae k j)) (dotDown zl fun k => cZ.P.Ae k j)))
    rw [toReal_neg] at e1 e2
    rw [ConZonotope.aux_resDown]
    linarith
  -- the upper end, its three additions rounded up
  · have e1 := add_le_addUp (neg (dotDown zu fun k => cZ.P.Ae k j))
      (dotUp zl fun k => cZ.P.Ae k j)
    have e2 := add_le_addUp (neg (dotDown y fun k => cZ.P.A k j))
      (addUp (neg (dotDown zu fun k => cZ.P.Ae k j)) (dotUp zl fun k => cZ.P.Ae k j))
    have e3 := add_le_addUp (dotUp a (cZ.G j))
      (addUp (neg (dotDown y fun k => cZ.P.A k j))
        (addUp (neg (dotDown zu fun k => cZ.P.Ae k j)) (dotUp zl fun k => cZ.P.Ae k j)))
    rw [toReal_neg] at e1 e2
    rw [ConZonotope.aux_resUp]
    linarith


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficient program bounded at the given weights, each clamped at zero,
the residual paid by the unit box. Sound for every weight vector. -/
def ConZonotope.nominalBoundWeights (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (y₀ : Vec 𝕋 cZ.P.m) (zu₀ zl₀ : Vec 𝕋 cZ.P.me) : FloatBound 𝕋 (nominalSet cZ) c :=
  let y : Vec 𝕋 cZ.P.m := fun k => ConZonotope.aux_clamp (y₀ k)
  let zu : Vec 𝕋 cZ.P.me := fun k => ConZonotope.aux_clamp (zu₀ k)
  let zl : Vec 𝕋 cZ.P.me := fun k => ConZonotope.aux_clamp (zl₀ k)
  let R : Vec 𝕋 cZ.h := fun j =>
    maximum (ConZonotope.aux_resUp cZ a y zu zl j) (neg (ConZonotope.aux_resDown cZ a y zu zl j))
  -- the right-hand sides, each widened by its row's slack, rounded up: the constraint's own
  let bS : Vec 𝕋 cZ.P.m := cZ.P.bSlackU
  let beU : Vec 𝕋 cZ.P.me := cZ.P.beSlackU
  let beL : Vec 𝕋 cZ.P.me := cZ.P.beSlackLN
  { val := addUp (dotUp a cZ.c) (addUp (dotUp y bS) (addUp (dotUp zu beU)
      (addUp (dotUp zl beL) (sumUp R))))
    le := by
      intro x hx
      obtain ⟨β, hβ, hP, hxβ⟩ := ConZonotope.mem_nominalSet_iff.mp hx
      obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hP
      -- the clamped weights are admissible, whatever was proposed
      have hy : ∀ k, 0 ≤ toReal (y k) := fun k => ConZonotope.aux_clamp_nonneg _
      have hzu : ∀ k, 0 ≤ toReal (zu k) := fun k => ConZonotope.aux_clamp_nonneg _
      have hzl : ∀ k, 0 ≤ toReal (zl k) := fun k => ConZonotope.aux_clamp_nonneg _
      -- the rows' images of `β`, spelt as sums
      have hAβ : ∀ k, (toRealMat cZ.P.A *ᵥ β) k = ∑ j, toReal (cZ.P.A k j) * β j :=
        fun _ => rfl
      have hAeβ : ∀ k, (toRealMat cZ.P.Ae *ᵥ β) k = ∑ j, toReal (cZ.P.Ae k j) * β j :=
        fun _ => rfl
      -- the residual, column by column
      set D : Fin cZ.h → ℝ := fun j => ∑ i, toReal (a i) * toReal (cZ.G j i) with hD
      set Y : Fin cZ.h → ℝ := fun j => ∑ k, toReal (y k) * toReal (cZ.P.A k j) with hY
      set U : Fin cZ.h → ℝ := fun j => ∑ k, toReal (zu k) * toReal (cZ.P.Ae k j) with hU
      set L : Fin cZ.h → ℝ := fun j => ∑ k, toReal (zl k) * toReal (cZ.P.Ae k j) with hL
      -- `c x` is the center's reading plus the coefficients against `Gᵀa`
      have hcx : c x = (∑ i, toReal (a i) * toReal (cZ.c i)) + ∑ j, β j * D j := by
        rw [hc x]
        simp_rw [hxβ, mul_add, Finset.sum_add_distrib]
        rw [ConZonotope.aux_sum_swap (fun i => toReal (a i)) (fun i j => toReal (cZ.G j i)) β]
      -- the split of `βᵀD` into residual and rows
      have hsplit : ∑ j, β j * D j
          = (∑ j, β j * (D j - Y j - U j + L j)) + (∑ j, β j * Y j) + (∑ j, β j * U j)
            - ∑ j, β j * L j := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring
      -- weak duality, row block by row block: each row within its widened right-hand side
      have hbS : ∀ k, (toRealMat cZ.P.A *ᵥ β) k ≤ toReal (bS k) := fun k => by
        have h := add_le_addUp (cZ.P.b k) (absolute (cZ.P.b_error k))
        rw [toReal_absolute] at h
        exact (hle k).trans h
      have hbeU : ∀ k, (toRealMat cZ.P.Ae *ᵥ β) k ≤ toReal (beU k) := fun k => by
        have h := add_le_addUp (cZ.P.be k) (absolute (cZ.P.be_error k))
        rw [toReal_absolute] at h
        show _ ≤ toReal (addUp (cZ.P.be k) (absolute (cZ.P.be_error k)))
        linarith [(abs_le.mp (heq k)).2]
      have hbeL : ∀ k, -toReal (beL k) ≤ (toRealMat cZ.P.Ae *ᵥ β) k := fun k => by
        have h := add_le_addUp (neg (cZ.P.be k)) (absolute (cZ.P.be_error k))
        rw [toReal_absolute, toReal_neg] at h
        show -toReal (addUp (neg (cZ.P.be k)) (absolute (cZ.P.be_error k))) ≤ _
        linarith [(abs_le.mp (heq k)).1]
      -- the inequality block and the equality block's upper edge, weighted
      have hYb : ∑ j, β j * Y j ≤ toReal (dotUp y bS) := by
        rw [hY, ← ConZonotope.aux_sum_swap (fun k => toReal (y k))
          (fun k j => toReal (cZ.P.A k j)) β]
        refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_dotUp _ _)
        rw [← hAβ]
        exact mul_le_mul_of_nonneg_left (hbS k) (hy k)
      have hUb : ∑ j, β j * U j ≤ toReal (dotUp zu beU) := by
        rw [hU, ← ConZonotope.aux_sum_swap (fun k => toReal (zu k))
          (fun k j => toReal (cZ.P.Ae k j)) β]
        refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_dotUp _ _)
        rw [← hAeβ]
        exact mul_le_mul_of_nonneg_left (hbeU k) (hzu k)
      -- the lower edge of an equality row, read through its negated row
      have hLb : -toReal (dotUp zl beL) ≤ ∑ j, β j * L j := by
        rw [hL, ← ConZonotope.aux_sum_swap (fun k => toReal (zl k))
          (fun k j => toReal (cZ.P.Ae k j)) β]
        have hd := neg_le_neg (le_dotUp zl beL)
        refine le_trans hd ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← hAeβ, ← mul_neg]
        exact mul_le_mul_of_nonneg_left (hbeL k) (hzl k)
      -- the box pays for the residual
      have hRb : ∑ j, β j * (D j - Y j - U j + L j) ≤ toReal (sumUp R) := by
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp R)
        obtain ⟨hlo, hhi⟩ := ConZonotope.aux_res_encl cZ a y zu zl j
        have habs : |D j - Y j - U j + L j| ≤ toReal (R j) := by
          show _ ≤ toReal (maximum _ _)
          rw [toReal_maximum, toReal_neg]
          refine abs_le.mpr ⟨?_, ?_⟩
          · have := le_max_right (toReal (ConZonotope.aux_resUp cZ a y zu zl j))
              (-toReal (ConZonotope.aux_resDown cZ a y zu zl j))
            linarith
          · exact le_trans hhi (le_max_left _ _)
        -- `|βⱼ| ≤ 1` is the box
        calc β j * (D j - Y j - U j + L j) ≤ |β j * (D j - Y j - U j + L j)| := le_abs_self _
          _ = |β j| * |D j - Y j - U j + L j| := abs_mul _ _
          _ ≤ 1 * |D j - Y j - U j + L j| :=
            mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
          _ ≤ toReal (R j) := by rw [one_mul]; exact habs
      -- the four outer additions, each rounded up
      have hc0 := le_dotUp a cZ.c
      have r1 := add_le_addUp (dotUp zl beL) (sumUp R)
      have r2 := add_le_addUp (dotUp zu beU) (addUp (dotUp zl beL) (sumUp R))
      have r3 := add_le_addUp (dotUp y bS) (addUp (dotUp zu beU) (addUp (dotUp zl beL) (sumUp R)))
      have r4 := add_le_addUp (dotUp a cZ.c) (addUp (dotUp y bS)
        (addUp (dotUp zu beU) (addUp (dotUp zl beL) (sumUp R))))
      rw [hcx, hsplit]
      linarith }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
