module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A zonotope as an ellipsoid

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.1]: the zonotope lies in the ellipsoid of its bounding box,
`Z ⊆ [c − β, c + β] ⊆ E(n diag(β²), c)`. -/
theorem Zonotope.ellipsoidBox_contains (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.ellipsoidBox.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  -- the offset in coordinate `i` is at most the box radius `bᵢ = ∑ⱼ |Gⱼᵢ|`
  set b : Fin n → ℝ := fun i => ∑ j, |Z.G j i| with hb
  have hoff : ∀ i, |(∑ j, β j • Z.G j) i| ≤ b i := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ j)
  -- coordinates of the ball point: `oᵢ / (√n bᵢ)`, or `0` on a degenerate axis
  set o : Vec ℝ n := ∑ j, β j • Z.G j with ho
  refine ⟨fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i), ?_, ?_⟩
  · -- each squared coordinate is at most `1/n`
    have hu : ∀ i, (if b i = 0 then 0 else o i / (Real.sqrt n * b i)) ^ 2 ≤ 1 / (n : ℝ) := by
      intro i
      have hn : (0:ℝ) < n := by exact_mod_cast i.pos
      by_cases h0 : b i = 0
      · simp [h0]
      · have hbpos : 0 < b i := lt_of_le_of_ne
          (Finset.sum_nonneg fun j _ => abs_nonneg _) (Ne.symm h0)
        simp only [h0, if_false]
        have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
        rw [div_pow, mul_pow, hsq, div_le_div_iff₀ (by positivity) hn]
        have := sq_le_sq' (abs_le.1 (hoff i)).1 (abs_le.1 (hoff i)).2
        nlinarith [mul_nonneg hn.le (sq_nonneg (b i))]
    -- so the squares sum to at most `1`
    have hsum : ∑ i, (if b i = 0 then 0 else o i / (Real.sqrt n * b i)) ^ 2 ≤ 1 := by
      calc _ ≤ ∑ _i : Fin n, 1 / (n : ℝ) := Finset.sum_le_sum fun i _ => hu i
        _ = (n : ℝ) * (1 / (n : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · rw [h0]; norm_num
            · have hh : (0:ℝ) < n := by exact_mod_cast h0
              exact le_of_eq (by rw [mul_one_div, div_self hh.ne'])
    calc ‖fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i)‖₂ ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  · -- and the diagonal generator maps it back to the offset
    funext i
    show (Z.c + o) i = Z.c i + (Matrix.diagonal (fun i => Real.sqrt n * b i) *ᵥ
      fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i)) i
    rw [Matrix.mulVec_diagonal]
    by_cases h0 : b i = 0
    · have : o i = 0 := abs_nonpos_iff.1 (by simpa [h0] using hoff i)
      simp [h0, this]
    · have hn : (0:ℝ) < n := by exact_mod_cast i.pos
      simp only [h0, if_false, Pi.add_apply]
      have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
      field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
