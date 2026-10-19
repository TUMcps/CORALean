module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullBlock
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullLast
public import CORALean.ContSet.ConPolyZono.Float.Theorems.AbsSubLeSubUp
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.Global.Float.IntRound
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# The stored hull's constraints hold wherever the copies' and the weights' do

Read back, the stored constraint matrix is the exact layer's on the read-back operand: copies,
`zero` and `one` round nothing. So a copy's row is the operand's at that copy's factors
(`mulVec_convHull_block`), held to the operand's right-hand side and slack, and the weight row is
the weights' sum (`mulVec_convHull_last`), held to `1 - a` stored from below with the gap to the
upward rounding as its slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Read back, the stored matrix is the exact layer's. -/
theorem ConPolyZono.aux_toRealMat_convHullA (a : ℕ) {m q : ℕ} (A : Mat 𝕋 m q) :
    toRealMat (ConPolyZono.convHullA a A)
      = Real.ConPolyZono.convHullA a (toRealMat A) := by -- --- PROOF ---
  funext x y
  refine Fin.addCases (fun r => ?_) (fun r => ?_) x <;>
    refine Fin.addCases (fun l => ?_) (fun l => ?_) y <;>
    simp only [toRealMat, ConPolyZono.convHullA, Real.ConPolyZono.convHullA, Fin.append_left,
      Fin.append_right, toReal_zero, toReal_one]
  -- the diagonal blocks: an entry of a block, or `zero`
  unfold ConPolyZono.blkDiag Real.ConPolyZono.blkDiag
  split_ifs
  · rfl
  · exact toReal_zero


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.convHullSingle_satisfies_of_real (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (v : Fin (a * cPZ.p + a) → ℝ)
    (hcopy : ∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ cPZ.cons.construct)
    (hw : ∑ j, v (Fin.natAdd (a * cPZ.p) j) = 1 - (a : ℝ)) : -- --- STMT ---
    v ∈ (cPZ.convHullSingle a).cons.construct := by -- --- PROOF ---
  refine (PolyLevelSet.mem_construct_iff_of_eq (cPZ.convHullSingle a).cons_eq).mpr fun i => ?_
  show |(toRealMat (ConPolyZono.convHullA a cPZ.cons.A) *ᵥ Real.PolyZonotope.monomial
      (Real.ConPolyZono.convHullR a cPZ.cons.R) v) i
          - toReal (ConPolyZono.convHullB a cPZ.cons.b i)|
    ≤ |toReal (Fin.append (Real.ConPolyZono.repVec a cPZ.cons.b_error)
      (fun _ => subUp (intUp (1 - (a : ℤ))) (intDown (1 - (a : ℤ)))) i)|
  rw [ConPolyZono.aux_toRealMat_convHullA]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) i
  -- a copy's row: the operand's, at that copy's factors
  · obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [Real.ConPolyZono.mulVec_convHull_block]
    simpa only [ConPolyZono.convHullB, Real.ConPolyZono.repVec, Fin.append_left,
      Equiv.symm_apply_apply] using
        (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp (hcopy j) k
  -- the weight row: the weights' sum, `1 - a` exactly, stored between its two roundings
  · have hr : r = 0 := Subsingleton.elim r 0
    subst hr
    rw [Real.ConPolyZono.mulVec_convHull_last, hw]
    simp only [ConPolyZono.convHullB, Fin.append_right]
    obtain ⟨h₁, h₂⟩ := intDown_le_intUp (𝕋 := 𝕋) (1 - (a : ℤ))
    push_cast at h₁ h₂
    exact ConPolyZono.abs_sub_le_subUp h₁ h₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
