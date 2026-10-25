module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

@[expose] public section

/-!
# Boxing what a partition drops in a basis over-approximates

`reduceBy_outer` again, with the axes replaced by the columns of an invertible `P`, holding at
every such `P` as that one holds at every partition — so a rule choosing `P` contributes tightness
and never soundness. Each dropped generator is read in `P`'s coordinates as `P⁻¹ g`, whose rows
the new block bounds; `coefficient` rescales as before, and `P * P⁻¹ = 1` is the only place
invertibility is used — it turns the recovered coordinates back into the reach they came from.
At a singular `P` the statement is unavailable: Mathlib's `P⁻¹` is then zero, the new block
collapses, and nothing encloses; CORA reaches the same place by a pseudoinverse and does not test
for it. This is [1, Prop. 9].

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices
* `P` – basis matrix

## Hypotheses
* `hP` – `P` invertible

## Conclusion
* `Z` lies in the reduced zonotope

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `reduceByBasis`'s generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sumUnivReduceByBasis {Z : Zonotope (Vec ℝ n)}
    {part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)} {P : Mat ℝ n n} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceByBasis part P).h, f j =
      ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what a partition drops along an invertible `P`'s columns
over-approximates, whichever partition and whichever `P`. -/
theorem Zonotope.reduceByBasis_outer (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) {P : Mat ℝ n n}
    (hP : IsUnit P.det) : -- --- CONCL ---
    Z.construct ⊆ (Z.reduceByBasis part P).construct := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  -- the dropped reach in `P`'s coordinates, bounded row by row
  have hbound : ∀ k, |∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l)|
      ≤ ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k| := by
    intro k
    calc |∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l)|
        ≤ ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k| := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l)) (abs_nonneg _)
  have hnonneg : ∀ k, (0:ℝ) ≤ ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k| :=
    fun k => (abs_nonneg _).trans (hbound k)
  -- the witness: kept coefficients, plus one per column of `P`
  refine Zonotope.mem_construct_iff.mpr
    ⟨Fin.append (fun l => β (part.left l)) (fun k =>
      Zonotope.coefficient (∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|)
        (∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun k => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg k) (hbound k)
  -- `P` undoes `P⁻¹` on every dropped generator, which is where `hP` is spent
  · have hPP : ∀ l, ∑ k, P i k * (P⁻¹ *ᵥ Z.G (part.right l)) k = Z.G (part.right l) i := by
      intro l
      have h1 : P *ᵥ (P⁻¹ *ᵥ Z.G (part.right l)) = Z.G (part.right l) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [← Matrix.mulVec_apply_eq_sum, h1]
    -- each new generator carries one recovered coordinate, and `P` sums them back
    have hkey : ∑ k, P i k * (∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|) *
        Zonotope.coefficient (∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|)
          (∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l))
        = ∑ l, Z.G (part.right l) i * β (part.right l) := by
      calc ∑ k, P i k * (∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|) *
              Zonotope.coefficient (∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|)
                (∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l))
          = ∑ k, P i k * ∑ l, (P⁻¹ *ᵥ Z.G (part.right l)) k * β (part.right l) :=
            Finset.sum_congr rfl fun k _ => by
              rw [mul_assoc, Zonotope.mul_coefficient (hbound k)]
        _ = ∑ l, Z.G (part.right l) i * β (part.right l) := by
            simp_rw [Finset.mul_sum, ← mul_assoc]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun l _ => by rw [← Finset.sum_mul, hPP l]
    rw [hx i, part.sum_split₂ fun j => Z.G j i * β j, Zonotope.aux_sumUnivReduceByBasis]
    simp only [Zonotope.reduceByBasis, Fin.append_left, Fin.append_right]
    rw [hkey]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
