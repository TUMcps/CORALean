module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStepFloat
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.LinStepLinInputOuter
public import CORALean.ContSet.ContSet.Theorems.IntersectStripSeqOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# The nonlinear float observer step encloses

[1, Alg. 1] and [2, Eq. 4], one step, for a nonlinear system: a state `x` of a set inside
`X̂`, within the certificate's region, stepped by `x ↦ f(x, u) + ω` with `u` in the input set
and `ω` in `W`, whose output meets the strip, lies in the zonotope `observeStepFloat`
returns, whatever the gain. The prediction is `NonlinearSysDT.reach`'s step
(`reach_one_outer` on the widened input); an outer statement, the strips read as real numbers at
the stored values.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.observeStepFloat_outer (sys : NonlinearSysDT n m) {U : Zonotope (Vec 𝕋 m)}
    (step : sys.LinStep (S := 𝒵[𝕋]) 𝕋 U) (o : NonlinearSysDT.ReachOptions)
    (C : Mat 𝕋 p n) (σ : Vec 𝕋 p) (W : Zonotope (Vec 𝕋 n))
    (options : LinearSysDT.ObserveStripOptions 𝕋 (Zonotope (Vec 𝕋 n)) n p) (y : Vec 𝕋 p)
    (Xhat : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n} {u : Vec ℝ m} {w : Vec ℝ n}
    (hx : x ∈ Xhat.construct) (hR : x ∈ step.R) (hu : u ∈ construct U) (hw : w ∈ W.construct)
    (hy : ∀ i, |(Scalar.toRealMat C *ᵥ (sys.f x u + w) - Scalar.toRealVec y) i|
      ≤ Scalar.toReal (σ i)) : -- --- CONCL ---
    sys.f x u + w ∈
      (sys.observeStepFloat step o C σ W options y Xhat).construct := by -- --- PROOF ---
  -- the prediction: the linearized step on the widened input holds `f(x, u)`
  have key := LinearSysDT.reach_one_outer (S := 𝒵[𝕋])
    (NonlinearSysDT.linearize step.A) o.hZonotopeOrder
    Xhat step.linInput hx (step.linInput_outer hR hu)
  have heq : Scalar.toRealMat (NonlinearSysDT.linearize step.A).A *ᵥ x
      + (sys.f x u - Scalar.toRealMat step.A *ᵥ x) = sys.f x u := by
    show Scalar.toRealMat step.A *ᵥ x + (sys.f x u - Scalar.toRealMat step.A *ᵥ x) = sys.f x u
    abel
  rw [heq] at key
  -- plus the disturbance, then the update; one step of `reach` is read off `Nat.fold`
  have hone : sys.reach (S := 𝒵[𝕋]) ⟨Xhat, U, 0, 1⟩ o (fun _ => step)
      = (NonlinearSysDT.linearize step.A).reach (S := 𝒵[𝕋])
        ⟨Xhat, step.linInput, 0, 1⟩ ⟨o.ρ, o.hZonotopeOrder⟩ := by
    show Nat.fold (1 - 0) _ Xhat = _
    rw [Nat.sub_zero, Nat.fold_succ, Nat.fold_zero]
  have hpred : sys.f x u + w ∈
    ((sys.reach (S := 𝒵[𝕋]) ⟨Xhat, U, 0, 1⟩ o (fun _ => step)).plus
      W).construct := by
    rw [hone]
    exact Zonotope.plus_outer _ _ ⟨_, key, w, hw, rfl⟩
  unfold NonlinearSysDT.observeStepFloat
  split
  · exact ContSet.intersectStripSeq_outer (S := 𝒵[𝕋]) _ _ _ _ _ ⟨hpred, hy⟩
  · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨hpred, hy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
