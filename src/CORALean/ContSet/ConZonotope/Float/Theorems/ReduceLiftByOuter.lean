module

public import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemKeepColsNominal
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# Lifting, reducing and reading the rows back over-approximates, in floats

[1, Sec. 4.3] on the stored floats.

A point `y + e` of `cZ`, `y` nominal at `β`: `Zonotope.aux_reduceBy_coeff` on the lifted zonotope
gives coefficients `ξ` that agree with `β` on the kept generators and reproduce every
coordinate of the lifted sum. The upper coordinates are `y`, so the point is the result's
nominal point at `ξ` plus the same `e`. The lower coordinates are `Aₑ β`, which the new
equality rows read at `ξ` as the same number, within the carried slack of the unchanged `bₑ`. The
inequality rows at `ξ` are those at `β` on the kept generators (`HPolytope.mem_keepCols_nominal`).

## Inputs
* `cZ` – float constrained zonotope
* `part` – generator partition

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Zonotope.reduceBy` carries the coefficients of the kept generators over. -/
theorem Zonotope.aux_reduceBy_coeff (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (β : Fin Z.h → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ∃ ξ : Fin (q + n) → ℝ, (∀ j, |ξ j| ≤ 1) ∧ (∀ l, ξ (Fin.castAdd n l) = β (part.left l))
      ∧ ∀ i, ∑ j, toReal (Z.G j i) * β j
        = ∑ j : Fin (q + n), toReal ((Z.reduceBy part).G j i) * ξ j := by -- --- PROOF ---
  -- the dropped reach is nonnegative and inside the rounded radius
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |toReal (Z.G (part.right l) i)| :=
    fun i => Finset.sum_nonneg fun l _ => abs_nonneg _
  have hle : ∀ i, (∑ l, |toReal (Z.G (part.right l) i)|)
      ≤ toReal (radius (fun i l => Z.G (part.right l) i) i) :=
    fun i => sum_abs_le_radius (d := fun i l => Z.G (part.right l) i) i
  -- what the dropped generators contribute at coordinate `i`, inside the rounded radius
  have hbound : ∀ i, |∑ l, toReal (Z.G (part.right l) i) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G (part.right l) i) i) := by
    intro i
    refine le_trans ?_ (hle i)
    calc |∑ l, toReal (Z.G (part.right l) i) * β (part.right l)|
        ≤ ∑ l, |toReal (Z.G (part.right l) i) * β (part.right l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |toReal (Z.G (part.right l) i)| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |toReal (Z.G (part.right l) i)| := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (toReal (Z.G (part.right l) i)))
  -- the witness: kept coefficients, then one per coordinate scaled to the dropped reach
  refine ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      Real.Zonotope.coefficient (toReal (radius (fun i l => Z.G (part.right l) i) i))
        (∑ l, toReal (Z.G (part.right l) i) * β (part.right l))), ?_, fun l => ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one ((hnonneg i).trans (hle i)) (hbound i)
  · simp
  -- the generator sums agree, the box block through its diagonal
  · rw [part.sum_split₂ fun j => toReal (Z.G j i) * β j, Fin.sum_univ_add]
    simp only [Zonotope.reduceBy, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul']
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLiftBy_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.reduceLiftBy part).construct := by -- --- PROOF ---
  rintro x ⟨y, hy', e, he, hx⟩
  obtain ⟨β, hβ, hP, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  obtain ⟨hPin, hPeq⟩ := HPolytope.mem_nominal_iff.mp hP
  obtain ⟨ξ, hξ, hξl, hsum⟩ := Zonotope.aux_reduceBy_coeff cZ.liftEq part β hβ
  refine ⟨y, ConZonotope.mem_nominalSet_iff.mpr ⟨ξ, hξ, ?_, fun k => ?_⟩, e, he, hx⟩
  · refine HPolytope.mem_stackRows_nominal_iff.mpr ⟨?_, HPolytope.mem_nominal_iff.mpr
      ⟨fun i => i.elim0, fun i => ?_⟩⟩
    · -- the inequality rows: the kept coefficients, the fresh ones read as zero
      show ξ ∈ (((cZ.P.keepCols part).dropEqs).padLeft (n + cZ.P.me)).nominal.construct
      rw [HPolytope.mem_padLeft_nominal_iff]
      have hk := HPolytope.mem_keepCols_nominal cZ.P part hP fun l => hβ (part.right l)
      have hl : blockLeft q (n + cZ.P.me) ξ = fun l => β (part.left l) := funext hξl
      rw [hl]
      exact HPolytope.mem_nominal_iff.mpr ⟨(HPolytope.mem_nominal_iff.mp hk).1, fun i => i.elim0⟩
    · -- the lower coordinates of the lifted sum are the original equality rows
      have heq := hPeq i
      simp only [mulVec, dotProduct, toRealMat] at heq ⊢
      have hs := hsum (Fin.natAdd n i)
      simp only [ConZonotope.liftEq, Fin.append_right] at hs
      have key : ∑ j : Fin (cZ.liftEq.reduceBy part).h,
          toReal ((cZ.liftEq.reduceBy part).G j (Fin.natAdd n i)) * ξ j
          = ∑ j, toReal (cZ.P.Ae i j) * β j := hs.symm
      exact key ▸ heq
  · -- the upper coordinates are the point itself
    have hs := hsum (Fin.castAdd cZ.P.me k)
    simp only [ConZonotope.liftEq, Fin.append_left] at hs
    rw [hy k]
    exact congrArg (toReal (cZ.c k) + ·) hs

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
