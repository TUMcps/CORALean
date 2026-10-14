module

public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# What a point of `halfScaledLeft` says about its first block

The converse of `smul_mem_halfScaledLeft`: a coefficient vector in the weighted polytope has its
first block meeting `P`'s rows at the weight `(t + 1) / 2` its trailing coordinate names, an
inequality's bound and an equality's interval both scaled by it. Nothing is said of the middle
block, which the polytope never reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_halfScaledLeft {P : HPolytope 𝕋 (Vec 𝕋 n₁)} {y : Vec ℝ n₁}
    {z : Vec ℝ n₂} {t : ℝ}
    (h : Fin.append (Fin.append y z) (fun _ : Fin 1 => t) ∈ (P.halfScaledLeft n₂).construct) :
    (∀ i, (toRealMat P.A *ᵥ y) i ≤ (t + 1) / 2 * toReal (P.b i)) ∧
      ∀ i, (t + 1) / 2 * toReal (P.be.inf i) ≤ (toRealMat P.Ae *ᵥ y) i ∧
        (toRealMat P.Ae *ᵥ y) i ≤ (t + 1) / 2 * toReal (P.be.sup i) := by -- --- PROOF ---
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
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append] at this
    simp only [toReal_neg, toReal_half] at this
    linarith
  · have := h3 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append, hneg,
      Matrix.neg_mulVec] at this
    simp only [Pi.neg_apply, toReal_neg, toReal_half] at this
    linarith
  · have := h2 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append] at this
    simp only [toReal_neg, toReal_half] at this
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
