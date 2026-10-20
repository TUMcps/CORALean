module

public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
public import CORALean.ContSet.ConZonotope.Real.Theorems.KeepRowsMem
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.Global.Entrywise
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# Boxing what a partition drops, and keeping its constraints, over-approximates

`Zonotope.reduceBy_outer`'s witness, with one more thing to check: the kept
coefficients `β ∘ left` still satisfy the constraints, which is `keepRows_mem`,
and the fresh ones are unconstrained. Whichever partition, as there.

## Inputs
* `cZ` – constrained zonotope
* `part` – generator partition

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The restatement `Fin.sum_univ_add` needs: the generator count is not
syntactically `q + n` until `reduceKeepBy` unfolds. -/
theorem ConZonotope.aux_sum_univ_reduceKeepBy {cZ : ConZonotope (Vec ℝ n)}
    {part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (cZ.reduceKeepBy part).h, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceKeepBy_outer (cZ : ConZonotope (Vec ℝ n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) :
    cZ.construct ⊆ (cZ.reduceKeepBy part).construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, hP, rfl⟩
  have hbound : ∀ i, |∑ l, cZ.G (part.right l) i * β (part.right l)|
      ≤ ∑ l, |cZ.G (part.right l) i| := by
    intro i
    calc |∑ l, cZ.G (part.right l) i * β (part.right l)|
        ≤ ∑ l, |cZ.G (part.right l) i * β (part.right l)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |cZ.G (part.right l) i| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |cZ.G (part.right l) i| := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (cZ.G (part.right l) i))
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |cZ.G (part.right l) i| :=
    fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: kept coefficients, then one per coordinate scaled to the dropped reach
  refine ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      Zonotope.coefficient (∑ l, |cZ.G (part.right l) i|)
        (∑ l, cZ.G (part.right l) i * β (part.right l))), ?_, ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  · -- the constraints see only the kept block, which `keepRows` admits
    show _ ∈ (HPolytope.comap (blockLeft q n) (ConZonotope.keepRows cZ.P part)).construct
    rw [HPolytope.comap_exact, Set.mem_preimage, blockLeft_append]
    exact ConZonotope.keepRows_mem cZ.P part hP fun l => hβ _
  · funext i
    -- the value: kept part as is, dropped part through the diagonal block
    rw [Entrywise.add_sum_smul_apply, Entrywise.add_sum_smul_apply,
      part.sum_split₂ fun j => cZ.G j i * β j]
    rw [ConZonotope.aux_sum_univ_reduceKeepBy]
    simp only [ConZonotope.reduceKeepBy, Zonotope.reduceBy, ConZonotope.zonotope]
    simp only [Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
