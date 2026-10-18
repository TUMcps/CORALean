module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStripBasedFloat
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ObserveStepFloatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter

@[expose] public section

/-!
# The nonlinear float strip-based observer holds the true state

[1, Alg. 1] over time, in floats, as CORA's `observe_stripBased` [2, Eq. 4] for a
`nonlinearSysDT`: every run `x_{k+1} = f(x_k, u_k) + ω_k` from `x_0 ∈ R₀` with `u_k` in the input
set, `ω_k ∈ W`, each state in its step's certified region, whose outputs meet every strip
`|C x_k - y_k| ≤ σ`, is in the observer's set at every step, whatever the gains and the order.
The confinement of the run to each step's region stays a hypothesis, as for
`NonlinearSysDT.reach_outer`. An outer statement; `𝕋 := ℝ` is the real case.

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

theorem NonlinearSysDT.observeStripBasedFloat_outer (sys : NonlinearSysDT n m)
    {U : Zonotope (Vec 𝕋 m)} (steps : ℕ → sys.LinStep (S := 𝒵[𝕋]) 𝕋 U)
    (o : NonlinearSysDT.ReachOptions)
    (C : Mat 𝕋 p n) (σ : Vec 𝕋 p) (W R₀ : Zonotope (Vec 𝕋 n)) (y : ℕ → Vec 𝕋 p)
    (options : LinearSysDT.ObserveStripOptions 𝕋 (Zonotope (Vec 𝕋 n)) n p)
    (x w : ℕ → Vec ℝ n)
    (u : ℕ → Vec ℝ m) (h0 : x 0 ∈ R₀.construct) (hu : ∀ k, u k ∈ construct U)
    (hw : ∀ k, w k ∈ W.construct) (hR : ∀ k, x k ∈ (steps k).R)
    (hstep : ∀ k, x (k + 1) = sys.f (x k) (u k) + w k)
    (hy : ∀ k i, |(Scalar.toRealMat C *ᵥ x k - Scalar.toRealVec (y k)) i|
      ≤ Scalar.toReal (σ i)) (k : ℕ) : -- --- STMT ---
    x k ∈ (sys.observeStripBasedFloat steps o C σ W R₀ y options k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    unfold NonlinearSysDT.observeStripBasedFloat
    split
    · exact ContSet.intersectStripSeq_outer (S := 𝒵[𝕋]) _ _ _ _ _ ⟨h0, hy 0⟩
    · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨h0, hy 0⟩
  | succ k ih =>
    unfold NonlinearSysDT.observeStripBasedFloat
    refine Zonotope.reduce_outer _ _ ?_
    have := sys.observeStepFloat_outer (steps k) o C σ W options (y (k + 1)) _ ih (hR k) (hu k)
      (hw k) (by rw [← hstep]; exact hy (k + 1))
    rwa [← hstep] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
