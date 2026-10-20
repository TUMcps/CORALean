module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyStep
public import CORALean.ContDynamics.LinearSys.Definitions.VerifySound
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact

@[expose] public section

/-!
# One iteration of `Alg. 3`: a safe verdict is sound

Lines 3-25 of [1, Alg. 3]. If the outer approximation's worst distance to leaving a safe set is `≤
0` and its distance to every unsafe set is `> 0`, the specification holds on every reached state:
`reachFn ε` contains them and `distG`/`distF` say what the signs mean.

## Inputs
* `Reach` – reachable set
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `le` – comparison oracle on reals
* `G` – safe polytopes
* `F` – unsafe polytopes
* `εmax` – maximal error

## Hypotheses
* `h` – the oracles are sound
* `hG` – the safe-set test passes
* `hF` – the unsafe-set test passes

## Conclusion
* the specification holds

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySpec_of_verifyStep {Reach : Set (Vec ℝ n)}
    {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ}
    {le : ℝ → ℝ → Bool} (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n)) (εmax : ℝ)
    (hG : (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGout ≤ 0)
    (hF : 0 < (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFout)
    : -- --- CONCL ---
    LinearSys.VerifySpec G F Reach := by -- --- PROOF ---
  -- the outer approximation, read as a constrained zonotope, still contains `Reach`
  have hR : Reach ⊆ (reachFn εmax).conZonotope.construct :=
    (Zonotope.conZonotope_exact (reachFn εmax)) ▸ h.outer εmax
  simp only [LinearSys.verifyStep] at hG hF
  refine ⟨fun j => ?_, fun j => ?_⟩
  · -- every `distG` is below the supremum, hence `≤ 0`
    have hj := (Finset.sup'_le_iff _ _).1 hG j (Finset.mem_univ j)
    exact hR.trans (h.distG_nonpos _ _ hj)
  · -- every `distF` is above the infimum, hence `> 0`
    have hj := (Finset.lt_inf'_iff _).1 hF j (Finset.mem_univ j)
    exact (h.distF_pos _ _ hj).mono_left hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
