import CORALean.ContDynamics.LinearSys.Operations.VerifyStep
import CORALean.ContDynamics.LinearSys.Definitions.VerifySound

/-!
# One iteration of `Alg. 3`: a falsified verdict is sound

Lines 3-25 of [1, Alg. 3]. If the inner approximation's best distance to leaving a safe set is `>
0`, or its distance to some unsafe set is `≤ 0`, a reached state breaks the specification:
`innerApprox` lies inside `Reach`, so what `distG`/`distF` say of it holds of `Reach`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.not_verifySpec_of_verifyStep {Reach : Set (Vec ℝ n)}
    {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ}
    {le : ℝ → ℝ → Bool} (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n)) (εmax : ℝ)
    (hfalse :
      0 < (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGin ∨
      (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFin ≤ 0) :
    ¬ LinearSys.VerifySpec G F Reach := by -- --- PROOF ---
  rintro ⟨hGspec, hFspec⟩
  simp only [LinearSys.verifyStep] at hfalse
  rcases hfalse with hG | hF
  · -- some `distG` is positive, so the inner approximation leaves that safe set
    obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 hG
    exact h.distG_pos _ _ hj ((h.inner _ _).trans (hGspec j))
  · -- some `distF` is nonpositive, so the inner approximation meets that unsafe set
    obtain ⟨j, -, hj⟩ := (Finset.inf'_le_iff _).1 hF
    exact h.distF_nonpos _ _ hj ((hFspec j).mono_left (h.inner _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
