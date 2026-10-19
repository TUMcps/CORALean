module

public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputsFloat
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapMixedOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadBilinApply

@[expose] public section

/-!
# `varInputsFloat` holds every value the varying input part can take

`[1, Eq. 7]` read as a membership, as `varInputs_outer` reads it, at the float stored matrices
`B` and `D` and the float sets: at any `z`, `z∆` and `u∆` drawn from the three, the second-order
part of `v∆` lies in `varInputsFloat`. One outer fact per piece — `mtimes` twice, `plus` three
times, `quadMapMixed` twice and `quadMap` once — after the double sum has been read back as the
three pairings. Outer only.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m o : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem varInputsFloat_outer (B : Mat 𝕋 n m) (D : Fin n → Mat 𝕋 o o)
    {Rz RzΔ : PolyZonotope (Vec 𝕋 o)} {UΔ : PolyZonotope (Vec 𝕋 m)} {z zΔ : Vec ℝ o} {uΔ : Vec ℝ m}
    (hz : z ∈ Rz.construct) (hzΔ : zΔ ∈ RzΔ.construct) (huΔ : uΔ ∈ UΔ.construct) : -- --- STMT ---
    (fun i => (toRealMat B *ᵥ uΔ) i
        + (2 : ℝ)⁻¹ * ∑ j, ∑ k, toReal (D i j k) * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k))
      ∈ (varInputsFloat B D Rz RzΔ UΔ).construct := by -- --- PROOF ---
  -- the paper's double sum is the three pairings, distributed and split
  have hsum : ∀ i, ∑ j, ∑ k, toReal (D i j k) * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k)
      = Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) z zΔ i
        + Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) zΔ z i
        + Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) zΔ zΔ i := by
    intro i
    rw [Real.PolyZonotope.quadBilin_apply, Real.PolyZonotope.quadBilin_apply,
      Real.PolyZonotope.quadBilin_apply]
    simp only [toRealMat, mul_add, Finset.sum_add_distrib]
  -- `½ I` acts as halving, entry by entry: only the diagonal term survives
  have hhalf : ∀ w : Vec ℝ n, toRealMat (aux_halfMat (𝕋 := 𝕋) n) *ᵥ w = (2 : ℝ)⁻¹ • w := by
    intro w
    funext i
    simp only [Matrix.mulVec, dotProduct, toRealMat, aux_halfMat, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [toReal_half, toReal_one]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
    · simp
  -- the value is then `B uΔ` plus half of the three pairings
  have hval : (fun i => (toRealMat B *ᵥ uΔ) i
        + (2 : ℝ)⁻¹ * ∑ j, ∑ k, toReal (D i j k) * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k))
      = toRealMat B *ᵥ uΔ + toRealMat (aux_halfMat (𝕋 := 𝕋) n) *ᵥ
          (Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) z zΔ
            + Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) zΔ z
            + Real.PolyZonotope.quadBilin (fun i => toRealMat (D i)) zΔ zΔ) := by
    rw [hhalf]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum i]
  rw [hval]
  -- `plus` of `B ⊗ U∆` and the halved sum of the three pairings
  refine PolyZonotope.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · exact PolyZonotope.mtimes_outer B UΔ ⟨uΔ, huΔ, rfl⟩
  · -- the halving is `mtimes` by `½ I`, of the sum of the three pairings
    refine PolyZonotope.mtimes_outer _ _ ⟨_, ?_, rfl⟩
    refine PolyZonotope.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · refine PolyZonotope.plus_outer _ _ (Set.add_mem_add ?_ ?_)
      · exact PolyZonotope.quadMapMixed_outer D Rz RzΔ ⟨(z, zΔ), ⟨hz, hzΔ⟩, rfl⟩
      · exact PolyZonotope.quadMapMixed_outer D RzΔ Rz ⟨(zΔ, z), ⟨hzΔ, hz⟩, rfl⟩
    · exact PolyZonotope.quadMap_outer D RzΔ ⟨zΔ, hzΔ, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
