import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBasedFloat
import CORALean.ContDynamics.LinearSysDT.Theorems.ObserveStepFloatOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter

/-!
# The float strip-based observer holds the true state

[1, Alg. 1] over time, in floats, as CORA's `observe_stripBased` [2, Eq. 4]: every run
`x_{k+1} = A x_k + u_k + ω_k` from `x_0 ∈ R₀` with `ω_k ∈ W`, whose outputs meet every strip
`|C x_k - y_k| ≤ σ`, is in the observer's set at every step, whatever the gains and the order. All
quantities are the real values of stored floats; an outer statement.

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

open Matrix CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStripBasedFloat_outer (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (σ : Vec 𝕋 p) (W R₀ : Zonotope (Vec 𝕋 n)) (u : ℕ → Vec 𝕋 n) (y : ℕ → Vec 𝕋 p)
    (options : LinearSysDT.ObserveStripOptionsFloat 𝕋 n p) (x w : ℕ → Vec ℝ n)
    (h0 : x 0 ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hstep : ∀ k, x (k + 1) = toRealMat sys.A *ᵥ x k + toRealVec (u k) + w k)
    (hy : ∀ k i, |(toRealMat C *ᵥ x k - toRealVec (y k)) i| ≤ toReal (σ i)) (k : ℕ) :
    x k ∈ (sys.observeStripBasedFloat C σ W R₀ u y options k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    unfold LinearSysDT.observeStripBasedFloat
    split
    · exact LinearSysDT.intersectStripSeqFloat_outer _ _ _ _ _ ⟨h0, hy 0⟩
    · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨h0, hy 0⟩
  | succ k ih =>
    unfold LinearSysDT.observeStripBasedFloat
    refine Zonotope.reduce_outer _ _ ?_
    refine sys.observeStepFloat_outer C σ W options (u k) (y (k + 1)) _
      (Set.singleton_subset_iff.mpr ih) ⟨⟨_, ⟨x k, rfl, rfl⟩, w k, hw k, ?_⟩, hy (k + 1)⟩
    rw [hstep]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
