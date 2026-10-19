module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.MulVecJoinInput
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatLeftCols
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatRightCols
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.SimulateBoxFloat
public import CORALean.NN.Theorems.EncloseOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The real closed-loop run lies in the float boxes

For a controller function `π` the network is `Sound` for, `simulate` from the real
value of a float start lies at every step in the box `simulateBox` computed in
float arithmetic: the float `simulate` row's guarantee (ruling R-SIM). An
enclosure, so the box is outer.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes ContSet CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_mem_simulateBox
    (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) ℐ𝒱[𝕋] n) (U_ext : Interval (Vec 𝕋 sys.nExt))
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π) {v : ℕ → Vec ℝ sys.nExt}
    (hv : ∀ k, v k ∈ construct U_ext) (x₀ : Vec 𝕋 n) (k : ℕ) : -- --- STMT ---
    sys.simulate π v (Scalar.toRealVec x₀) k ∈
      construct (sys.simulateBox U_ext x₀ k) := by -- --- PROOF ---
  induction k with
  | zero => exact Interval.mem_point x₀
  | succ k ih =>
    rw [show sys.simulate π v (Scalar.toRealVec x₀) (k + 1) =
      Scalar.toRealMat sys.plant.A *ᵥ sys.simulate π v (Scalar.toRealVec x₀) k +
        ((Scalar.toRealMat (leftCols sys.hm sys.plant.B) *ᵥ
          π (sys.simulate π v (Scalar.toRealVec x₀) k) +
          Scalar.toRealMat (rightCols sys.hm sys.plant.B) *ᵥ v k) +
          Scalar.toRealVec sys.plant.c) from by
      show sys.map π _ (v k) = _
      unfold NeurNetContrSysDT.map NeurNetContrSysDT.input
      rw [mulVec_joinInput, ← toRealMat_leftCols, ← toRealMat_rightCols, add_assoc]]
    -- `A x`, `B_nn π(x)`, `B_ext v` and `c` each in the box of its own term
    exact plus_outer (S := Interval (Vec 𝕋 n)) _ _
      (Set.add_mem_add (mtimes_outer (S := ℐ𝒱[𝕋]) sys.plant.A _
        (Set.mem_biUnion rfl (Set.mem_image_of_mem _ ih)))
        (plus_outer (S := Interval (Vec 𝕋 n)) _ _ (Set.add_mem_add
          (plus_outer (S := Interval (Vec 𝕋 n)) _ _ (Set.add_mem_add
            (mtimes_outer (S := ℐ𝒱[𝕋]) (leftCols sys.hm sys.plant.B) _
              (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hπ.enclose_outer _ _ ih))))
            (mtimes_outer (S := ℐ𝒱[𝕋]) (rightCols sys.hm sys.plant.B) _
              (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (hv k))))))
          (OfScalarPoint.mem_ofVec (S := ℐ𝒱[𝕋]) sys.plant.c))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
