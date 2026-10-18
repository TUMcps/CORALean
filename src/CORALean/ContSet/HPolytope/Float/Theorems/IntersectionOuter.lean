module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Theorems.AnchorEqsOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct

@[expose] public section

/-!
# `HPolytope.intersection` encloses

With both boxes certified empty of error, the intersection is exact
(`HPolytope.intersection_exact`). Otherwise a point of both polytopes satisfies each one's
inequalities raised by its box and reads within `beRes` of each equality
(`HPolytope.rows_of_mem_construct`), which is what `HPolytope.anchorEqs_outer` asks of it, with
the origin as the box it is shifted by.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_outer (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersection P₂).construct := by -- --- PROOF ---
  rintro x ⟨hx₁, hx₂⟩
  by_cases hc : (P₁.isErrFree && P₂.isErrFree) = true
  · simp only [Bool.and_eq_true] at hc
    exact HPolytope.intersection_exact hc.1 hc.2 ▸ ⟨hx₁, hx₂⟩
  rw [HPolytope.intersection, if_neg hc, ← add_zero x]
  obtain ⟨hA₁, hE₁⟩ := HPolytope.rows_of_mem_construct hx₁
  obtain ⟨hA₂, hE₂⟩ := HPolytope.rows_of_mem_construct hx₂
  -- an equality row reads within `beRes` of its bound, from the two widened halves
  have hres : ∀ (P : HPolytope 𝕋 (Vec 𝕋 n)),
      (∀ i, (toRealMat P.Ae *ᵥ x) i ≤ toReal (P.beU i)
        ∧ -(toRealMat P.Ae *ᵥ x) i ≤ toReal (P.beLN i)) →
      ∀ i, |(toRealMat P.Ae *ᵥ x) i - toReal (P.be i)| ≤ toReal (P.beRes i) := by
    intro P hE i
    have h1 := sub_le_subUp (P.beU i) (P.be i)
    have h2 := sub_le_subUp (P.beLN i) (neg (P.be i))
    rw [toReal_neg] at h2
    simp only [HPolytope.beRes, toReal_maximum]
    -- each side of the absolute value is one of the two widened halves
    rw [abs_le]
    constructor
    · linarith [(hE i).2, le_max_right (toReal (subUp (P.beU i) (P.be i)))
        (toReal (subUp (P.beLN i) (neg (P.be i))))]
    · linarith [(hE i).1, le_max_left (toReal (subUp (P.beU i) (P.be i)))
        (toReal (subUp (P.beLN i) (neg (P.be i))))]
  refine HPolytope.anchorEqs_outer _ _ (fun k => ?_) (fun k => ?_) fun j => ?_
  -- the inequalities, each half raised by its own box
  · refine le_add_of_le_of_nonneg ?_ (abs_nonneg _)
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · show (toRealMat (Fin.append P₁.A P₂.A) *ᵥ x) (Fin.castAdd P₂.m i)
        ≤ toReal (Fin.append P₁.bU P₂.bU (Fin.castAdd P₂.m i))
      rw [HPolytope.mulVec_append_left, Fin.append_left]
      exact hA₁ i
    · show (toRealMat (Fin.append P₁.A P₂.A) *ᵥ x) (Fin.natAdd P₁.m i)
        ≤ toReal (Fin.append P₁.bU P₂.bU (Fin.natAdd P₁.m i))
      rw [toRealMat_append_mulVec_natAdd, Fin.append_right]
      exact hA₂ i
  -- the equalities, each half within its own residual
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · show |(toRealMat (Fin.append P₁.Ae P₂.Ae) *ᵥ x) (Fin.castAdd P₂.me i)
          - toReal (Fin.append P₁.be P₂.be (Fin.castAdd P₂.me i))|
        ≤ toReal (Fin.append P₁.beRes P₂.beRes (Fin.castAdd P₂.me i))
      rw [HPolytope.mulVec_append_left, Fin.append_left, Fin.append_left]
      exact hres P₁ hE₁ i
    · show |(toRealMat (Fin.append P₁.Ae P₂.Ae) *ᵥ x) (Fin.natAdd P₁.me i)
          - toReal (Fin.append P₁.be P₂.be (Fin.natAdd P₁.me i))|
        ≤ toReal (Fin.append P₁.beRes P₂.beRes (Fin.natAdd P₁.me i))
      rw [toRealMat_append_mulVec_natAdd, Fin.append_right, Fin.append_right]
      exact hres P₂ hE₂ i
  -- the stacked rows carry the origin box
  · show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
