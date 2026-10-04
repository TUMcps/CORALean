import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStepFloat
import CORALean.ContDynamics.LinearSysDT.Theorems.IntersectStripSeqFloatOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

/-!
# The float observer step encloses

[1, Alg. 1] and [2, Eq. 4], one step: every state predicted from a state of `S ⊆ X̂` by
`x ↦ A x + u` with a disturbance of `W`, whose output meets the strip, lies in the zonotope
`observeStepFloat` returns, whatever the gain. An outer statement; the strips are read as real
numbers at the stored values.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStepFloat_outer (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (σ : Vec 𝕋 p) (W : Zonotope 𝕋 n) (options : LinearSysDT.ObserveStripOptionsFloat 𝕋 n p)
    (u : Vec 𝕋 n) (y : Vec 𝕋 p) (Xhat : Zonotope 𝕋 n) {S : Set (Vec ℝ n)}
    (hS : S ⊆ Xhat.construct) :
    ((fun x => toRealMat sys.A *ᵥ x + toRealVec u) '' S + W.construct) ∩
        {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (σ i)} ⊆
      (sys.observeStepFloat C σ W options u y Xhat).construct := by -- --- PROOF ---
  -- the prediction holds every predicted state
  have hpred : (fun x => toRealMat sys.A *ᵥ x + toRealVec u) '' S + W.construct ⊆
      ((Zonotope.plus (Zonotope.mtimes sys.A Xhat) (Zonotope.point u)).plus W).construct := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, w, hw, rfl⟩
    refine Zonotope.plus_outer _ _ ⟨_, Zonotope.plus_outer _ _ ⟨_, ?_, _, ?_, rfl⟩, w, hw, rfl⟩
    · exact Zonotope.mtimes_outer sys.A Xhat ⟨x, hS hx, rfl⟩
    · rw [Zonotope.construct_point]
      exact rfl
  intro x hx
  unfold LinearSysDT.observeStepFloat
  split
  · exact LinearSysDT.intersectStripSeqFloat_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩
  · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
