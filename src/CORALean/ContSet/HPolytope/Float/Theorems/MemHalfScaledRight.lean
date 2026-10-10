import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# What a point of `halfScaledRight` says about its second block

The converse of `smul_mem_halfScaledRight`: a coefficient vector in the weighted polytope has its
last block meeting `P`'s rows at the weight `(1 - t) / 2` its trailing coordinate names, an
inequality's bound and an equality's interval both scaled by it.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_halfScaledRight {P : HPolytope 𝕋 n₂} {z : Vec ℝ n₁} {y : Vec ℝ n₂} {t : ℝ}
    (h : Fin.append (Fin.append z y) (fun _ : Fin 1 => t)
      ∈ (HPolytope.halfScaledRight n₁ P).construct) :
    (∀ i, (toRealMat P.A *ᵥ y) i ≤ (1 - t) / 2 * toReal (P.b i)) ∧
      ∀ i, (1 - t) / 2 * toReal (P.be.inf i) ≤ (toRealMat P.Ae *ᵥ y) i ∧
        (toRealMat P.Ae *ᵥ y) i ≤ (1 - t) / 2 * toReal (P.be.sup i) := by -- --- PROOF ---
  have hneg : toRealMat (fun i' k => neg (P.Ae i' k)) = -toRealMat P.Ae := by
    funext i' k
    exact toReal_neg _
  -- the three row groups of the weighted polytope
  obtain ⟨h1, h2⟩ := HPolytope.mem_intersection_iff.mp h
  obtain ⟨h2, h3⟩ := HPolytope.mem_intersection_iff.mp h2
  have h1 := HPolytope.mem_ineqs_iff.mp h1
  have h2 := HPolytope.mem_ineqs_iff.mp h2
  have h3 := HPolytope.mem_ineqs_iff.mp h3
  -- each read on the block it came from
  refine ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · have := h1 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at this
    simp only [toReal_half] at this
    linarith
  · have := h3 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append, hneg,
      Matrix.neg_mulVec] at this
    simp only [Pi.neg_apply, toReal_neg, toReal_half] at this
    linarith
  · have := h2 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at this
    simp only [toReal_half] at this
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
