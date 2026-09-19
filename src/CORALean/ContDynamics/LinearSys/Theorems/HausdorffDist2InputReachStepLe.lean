import CORALean.ContDynamics.LinearSys.Theorems.HausdorffDist2InputReachLe
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.Global.EuclideanHausdorffDistAddLe

/-!
# [1, Prop. 2]: one step of the time-point error in the particular solution

Eq. (24)'s displayed recursion `ε^U_{k+1} = ε^U_k + Δε^U_k(Δt_k,η_k)`, one step of it. The exact
`P^U(t_k+Δt_k)` really does split as `P^U(t_k) ⊕ e^{At_k}P^U(Δt_k)` — `inputReach_separation_eq`,
Althoff's `Prop. 3.2` — so the recursively computed `P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)` is compared
summand by summand: `hausdorffDist₂_add_le` for the split, `hausdorffDist₂_inputReach_le`
(`Prop. 11`) for the new summand, and the error at `t_k` is the hypothesis eq. (24) reads it as.

Compactness of the four sets is what `Def. 5` asks of everything it measures, and is what makes
the nearest points in `hausdorffDist₂_add_le` exist. Eq. (21)'s accumulation over the horizon is
not proved here: it is an induction over a recursion this file does not name, and `Prop. 2`'s own
display is this single step.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

-- eight set-valued arguments to `hausdorffDist₂_add_le`, each re-solving the matrix instances
set_option maxHeartbeats 400000 in
/-- [1, Prop. 2], one step: the error at `t_k` plus eq. (25)'s one-step error bounds the distance
between `P^U(t_k+Δt_k)` and the recursively computed `P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)`. -/
theorem LinearSys.hausdorffDist₂_inputReach_step_le (sys : LinearSys 𝕋 n) {U : S n}
    {tk Δt : ℝ} (htk : 0 ≤ tk) (hΔt : 0 < Δt) (η : ℕ) {Pk : Set (Vec ℝ n)} {εk : ℝ}
    (hbdd : Bornology.IsBounded (construct U)) (hne : (construct U).Nonempty)
    (hcP : IsCompact (sys.inputReach U tk)) (hcPΔ : IsCompact (sys.inputReach U Δt))
    (hcQ : IsCompact Pk) (hQne : Pk.Nonempty)
    (hcQΔ : IsCompact (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η))
    (hstep : hausdorffDist₂ (sys.inputReach U tk) Pk ≤ εk)
    (houter : sys.inputReach U Δt
      ⊆ MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η) :
    hausdorffDist₂ (sys.inputReach U (tk + Δt))
        (Pk + (fun x => exp (tk • toRealMat sys.A) *ᵥ x)
          '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
      ≤ εk + MatExp.particularSolutionError
        (toRealMat sys.A) tk (construct U) Δt η := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  have hPne : (sys.inputReach U tk).Nonempty := ⟨_, sys.expIntegral_mem_inputReach htk hc⟩
  have hPΔne : (sys.inputReach U Δt).Nonempty := ⟨_, sys.expIntegral_mem_inputReach hΔt.le hc⟩
  have hQΔne : (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η).Nonempty :=
    hPΔne.imp fun _ hz => houter hz
  have hcont : Continuous (fun x : Vec ℝ n => exp (tk • toRealMat sys.A) *ᵥ x) :=
    (mulVecL (exp (tk • toRealMat sys.A))).continuous
  -- Althoff's `Prop. 3.2`: the exact set really is the sum the recursion mirrors
  have hsep : sys.inputReach U (tk + Δt)
      = sys.inputReach U tk
        + (fun y => exp (tk • toRealMat sys.A) *ᵥ y) '' sys.inputReach U Δt := by
    rw [add_comm tk Δt, sys.inputReach_separation_eq hΔt.le htk hbdd, add_comm]
  rw [hsep]
  refine (hausdorffDist₂_add_le hcP hPne hcQ hQne (hcPΔ.image hcont) (hPΔne.image _)
    (hcQΔ.image hcont) (hQΔne.image _)).trans (add_le_add hstep ?_)
  exact sys.hausdorffDist₂_inputReach_le tk hbdd hΔt η houter

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
