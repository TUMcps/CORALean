module

public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriExpand
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval

@[expose] public section

/-!
# The quadratic image of a point of `quadMapTri`'s operand, coefficient by coefficient

For a point `c + Σⱼ βⱼ gⱼ` of the operand, the quadratic form is `B₀₀ + ½ Σₛ Bₛₛ` plus the squares
with coefficient `2βₛ² - 1` and the pairs with coefficient `p'_r p'_j` (`quadMapTri_expand`), all
in `[-1, 1]`. The stored center and generators are rounded down, and what the exact center and
generators exceed them by is held by the box: the center's gap to its upper rounding, and each
generator's gap, which a coefficient in `[-1, 1]` spreads either way.

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – operand with a zero box
* `C` – the stored result
* `β` – factor vector of the operand

## Hypotheses
* `hC` – `C` is the result of `step_quadMapTriCore`
* `hβ` – factors in the unit box

## Conclusion
* the image has coefficients in the unit box and an error in the stored box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The coefficients of the quadratic image of the point `c + Σ βⱼ gⱼ` in `quadMapTri`'s result. -/
theorem Zonotope.quadMapTri_coeff (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n))
    (C : Zonotope (Vec 𝕋 m)) (hC : C = Zonotope.step_quadMapTriCore Q Z) (β : Fin Z.h → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ∃ γ : Fin C.h → ℝ, (∀ l, |γ l| ≤ 1) ∧ ∃ e ∈ C.I_error.toSet,
      Real.PolyZonotope.quadEval (fun k => toRealMat (Q k))
          (toRealVec Z.c + ∑ j, β j • toRealVec (Z.G j))
        = fun i => toReal (C.c i) + ∑ l, toReal (C.G l i) * γ l + e i := by -- --- PROOF ---
  subst hC
  -- the operand with its center in front, the entries `z_aᵀ Q z_b`, the exact center and generators
  set Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G with hZext
  set z : Fin (Z.h + 1) → Vec ℝ n := fun a => toRealVec (Zext a) with hz
  set B : Fin m → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ :=
    fun i a b => z a ⬝ᵥ (toRealMat (Q i) *ᵥ z b) with hB
  set cex : Fin m → ℝ := fun i => B i 0 0 + 1 / 2 * ∑ s : Fin Z.h, B i s.succ s.succ with hcex
  set gex : Fin m → Fin (Z.h + Zonotope.step_quadMapTriPairs Z.h) → ℝ := fun i =>
    Fin.append (fun s : Fin Z.h => 1 / 2 * B i s.succ s.succ)
      (fun u => B i (Zonotope.step_quadMapTriRow Z.h u) (Zonotope.step_quadMapTriCol Z.h u)
        + B i (Zonotope.step_quadMapTriCol Z.h u) (Zonotope.step_quadMapTriRow Z.h u)) with hgex
  -- the entries, bracketed
  have hent := fun i a b => Zonotope.quadMapTri_entry_bracket (Q i) Zext a b
  -- the center, bracketed: the squares' sum from either side, halving exact
  have hc : ∀ i, toReal (Zonotope.step_quadMapTriCDown Q Z i) ≤ cex i
      ∧ cex i ≤ toReal (Zonotope.step_quadMapTriCUp Q Z i) := by
    intro i
    have hs1 := sumDown_le_sum fun s : Fin Z.h =>
      half (Zonotope.step_quadMapTriEntryDown (Q i) Zext s.succ s.succ)
    have hs2 := sum_le_sumUp fun s : Fin Z.h =>
      half (Zonotope.step_quadMapTriEntryUp (Q i) Zext s.succ s.succ)
    have hlo : ∑ s : Fin Z.h, toReal (half (Zonotope.step_quadMapTriEntryDown (Q i) Zext
        s.succ s.succ)) ≤ ∑ s : Fin Z.h, 1 / 2 * B i s.succ s.succ :=
      Finset.sum_le_sum fun s _ => by
        rw [toReal_half]; linarith [(hent i s.succ s.succ).1]
    have hhi : ∑ s : Fin Z.h, 1 / 2 * B i s.succ s.succ ≤ ∑ s : Fin Z.h,
        toReal (half (Zonotope.step_quadMapTriEntryUp (Q i) Zext s.succ s.succ)) :=
      Finset.sum_le_sum fun s _ => by
        rw [toReal_half]; linarith [(hent i s.succ s.succ).2]
    -- the first entry plus the sum of the halved squares, each way
    have hd := addDown_le_add (Zonotope.step_quadMapTriEntryDown (Q i) Zext 0 0)
      (sumDown fun s : Fin Z.h =>
        half (Zonotope.step_quadMapTriEntryDown (Q i) Zext s.succ s.succ))
    have hu := add_le_addUp (Zonotope.step_quadMapTriEntryUp (Q i) Zext 0 0)
      (sumUp fun s : Fin Z.h =>
        half (Zonotope.step_quadMapTriEntryUp (Q i) Zext s.succ s.succ))
    have h0 := hent i 0 0
    simp only [Zonotope.step_quadMapTriCDown, Zonotope.step_quadMapTriCUp, hcex]
    constructor <;> simp only [Finset.mul_sum] at * <;> linarith [h0.1, h0.2]
  -- the generators, bracketed: the halved squares and the sums of two entries
  have hg : ∀ i l, toReal (Zonotope.step_quadMapTriGDown Q Z i l) ≤ gex i l
      ∧ gex i l ≤ toReal (Zonotope.step_quadMapTriGUp Q Z i l) := by
    intro i l
    refine Fin.addCases (fun s => ?_) (fun u => ?_) l
    · simp only [Zonotope.step_quadMapTriGDown, Zonotope.step_quadMapTriGUp, hgex,
        Fin.append_left, toReal_half]
      constructor <;> linarith [(hent i s.succ s.succ).1, (hent i s.succ s.succ).2]
    · -- the pair of two entries, each way
      simp only [Zonotope.step_quadMapTriGDown, Zonotope.step_quadMapTriGUp, hgex,
        Fin.append_right]
      have hd := addDown_le_add
        (Zonotope.step_quadMapTriEntryDown (Q i) Zext (Zonotope.step_quadMapTriRow Z.h u)
          (Zonotope.step_quadMapTriCol Z.h u))
        (Zonotope.step_quadMapTriEntryDown (Q i) Zext (Zonotope.step_quadMapTriCol Z.h u)
          (Zonotope.step_quadMapTriRow Z.h u))
      have hu := add_le_addUp
        (Zonotope.step_quadMapTriEntryUp (Q i) Zext (Zonotope.step_quadMapTriRow Z.h u)
          (Zonotope.step_quadMapTriCol Z.h u))
        (Zonotope.step_quadMapTriEntryUp (Q i) Zext (Zonotope.step_quadMapTriCol Z.h u)
          (Zonotope.step_quadMapTriRow Z.h u))
      have h1 := hent i (Zonotope.step_quadMapTriRow Z.h u) (Zonotope.step_quadMapTriCol Z.h u)
      have h2 := hent i (Zonotope.step_quadMapTriCol Z.h u) (Zonotope.step_quadMapTriRow Z.h u)
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the coefficients: `2βₛ² - 1` for the squares, `p'_r p'_j` for the pairs, each in `[-1, 1]`
  set q : Fin (Z.h + 1) → ℝ := Fin.cons 1 β with hq
  have hq1 : ∀ a, |q a| ≤ 1 := fun a => by
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [hq]
    · simpa [hq] using hβ j
  set γ : Fin (Z.h + Zonotope.step_quadMapTriPairs Z.h) → ℝ :=
    Fin.append (fun s : Fin Z.h => 2 * β s ^ 2 - 1)
      (fun u => q (Zonotope.step_quadMapTriRow Z.h u) * q (Zonotope.step_quadMapTriCol Z.h u))
    with hγ
  have hγ1 : ∀ l, |γ l| ≤ 1 := by
    intro l
    refine Fin.addCases (fun s => ?_) (fun u => ?_) l
    · simp only [hγ, Fin.append_left]
      have h1 := abs_le.mp (hβ s)
      rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
    · simp only [hγ, Fin.append_right, abs_mul]
      exact mul_le_one₀ (hq1 _) (abs_nonneg _) (hq1 _)
  refine ⟨γ, hγ1, ?_⟩
  -- the box holds the shortfall of the center and, per coefficient, of the generators
  have hd₁ : (fun i => cex i - toReal (Zonotope.step_quadMapTriCDown Q Z i))
      ∈ (Interval.residual (Zonotope.step_quadMapTriCDown Q Z)
        (Zonotope.step_quadMapTriCUp Q Z) (Zonotope.step_quadMapTriCDown Q Z)).toSet :=
    Interval.sub_mem_residual hc
  have hd₂ : (fun i => ∑ l, (gex i l - toReal (Zonotope.step_quadMapTriGDown Q Z i l)) * γ l)
      ∈ (Zonotope.generatorError fun i l => subUp (Zonotope.step_quadMapTriGUp Q Z i l)
          (Zonotope.step_quadMapTriGDown Q Z i l)).toSet := by
    refine Zonotope.mem_generatorError (fun i l => ?_) hγ1
    have hgap := sub_le_subUp (Zonotope.step_quadMapTriGUp Q Z i l)
      (Zonotope.step_quadMapTriGDown Q Z i l)
    rw [abs_of_nonneg (sub_nonneg.2 (hg i l).1)]
    linarith [(hg i l).2]
  refine ⟨_, Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, ?_⟩
  -- the quadratic form at the point, split as `quadMapTri_expand` splits it
  funext i
  have hx : toRealVec Z.c + ∑ j, β j • toRealVec (Z.G j) = z 0 + ∑ j, β j • z j.succ := by
    simp [hz, hZext]
  have hexp := Zonotope.quadMapTri_expand (toRealMat (Q i)) z β
  have hsplit : ∑ l, γ l * gex i l
      = ∑ s : Fin Z.h, (2 * β s ^ 2 - 1) * (1 / 2 * B i s.succ s.succ)
        + ∑ u : Fin (Zonotope.step_quadMapTriPairs Z.h),
            q (Zonotope.step_quadMapTriRow Z.h u) * q (Zonotope.step_quadMapTriCol Z.h u) *
              (B i (Zonotope.step_quadMapTriRow Z.h u) (Zonotope.step_quadMapTriCol Z.h u)
                + B i (Zonotope.step_quadMapTriCol Z.h u) (Zonotope.step_quadMapTriRow Z.h u)) := by
    rw [Fin.sum_univ_add]
    simp only [hγ, hgex, Fin.append_left, Fin.append_right]
  show Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) _ i = _
  simp only [Real.PolyZonotope.quadEval, hx]
  rw [hexp]
  -- the stored and the exact center and generators
  have hsum : ∑ l, toReal (Zonotope.step_quadMapTriGDown Q Z i l) * γ l
      + ∑ l, (gex i l - toReal (Zonotope.step_quadMapTriGDown Q Z i l)) * γ l
      = ∑ l, γ l * gex i l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  show _ = toReal (Zonotope.step_quadMapTriCDown Q Z i)
      + ∑ l, toReal (Zonotope.step_quadMapTriGDown Q Z i l) * γ l
      + (cex i - toReal (Zonotope.step_quadMapTriCDown Q Z i)
        + ∑ l, (gex i l - toReal (Zonotope.step_quadMapTriGDown Q Z i l)) * γ l)
  have hB' : ∀ a b, z a ⬝ᵥ (toRealMat (Q i) *ᵥ z b) = B i a b := fun a b => rfl
  simp only [hB'] at hexp ⊢
  rw [← hq] at hexp
  have hcex' : cex i = B i 0 0 + 1 / 2 * ∑ s : Fin Z.h, B i s.succ s.succ := rfl
  linarith [hsum, hsplit, hexp, hcex']

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
