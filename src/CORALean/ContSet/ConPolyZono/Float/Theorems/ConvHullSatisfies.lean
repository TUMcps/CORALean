import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsMono
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
import CORALean.Global.Float.IntRound

/-!
# The stored hull's constraints hold wherever the exact hull's do

Read back, the stored constraint matrix is the exact layer's on the read-back operand: copies,
`zero` and `one` round nothing. Only the weight row's bound differs, `1 - a` stored as an integer
enclosure, so the stored system admits every factor vector the exact one does.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Read back, the stored matrix is the exact layer's. -/
theorem ConPolyZono.aux_toRealMat_convHullA (a : ℕ) {m s : ℕ} (A : Mat 𝕋 m s) :
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
    (h : (Real.ConPolyZono.convHullSingle a (nominal cPZ)).satisfies v) :
    (cPZ.convHullSingle a).satisfies v := by -- --- PROOF ---
  unfold ConPolyZono.satisfies
  show Real.ConPolyZono.holds (toRealMat (ConPolyZono.convHullA a cPZ.A))
    (ConPolyZono.convHullB a cPZ.b).nominal (Real.ConPolyZono.convHullEC a cPZ.EC) v
  rw [ConPolyZono.aux_toRealMat_convHullA]
  have h' : Real.ConPolyZono.holds (Real.ConPolyZono.convHullA a (toRealMat cPZ.A))
      (Real.ConPolyZono.convHullB a cPZ.b.nominal) (Real.ConPolyZono.convHullEC a cPZ.EC) v := h
  refine Real.ConPolyZono.holds_mono (fun i => ?_) (fun i => ?_) h'
  -- the weight row's bound is an integer enclosure, the copies' are copied
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp [ConPolyZono.convHullB, Real.ConPolyZono.convHullB, Interval.nominal,
        RealImage.realImage, toRealVec, Real.ConPolyZono.repVec]
    · simp only [ConPolyZono.convHullB, Real.ConPolyZono.convHullB, Interval.nominal,
        RealImage.realImage, toRealVec, Fin.append_right]
      refine le_trans (intDown_le_intUp (𝕋 := 𝕋) _).1 ?_
      push_cast
      exact le_refl _
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp [ConPolyZono.convHullB, Real.ConPolyZono.convHullB, Interval.nominal,
        RealImage.realImage, toRealVec, Real.ConPolyZono.repVec]
    · simp only [ConPolyZono.convHullB, Real.ConPolyZono.convHullB, Interval.nominal,
        RealImage.realImage, toRealVec, Fin.append_right]
      refine le_trans ?_ (intDown_le_intUp (𝕋 := 𝕋) _).2
      push_cast
      exact le_refl _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
