module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetClosureConvexHull
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ZeroMemParticularSolutionOuter
public import CORALean.Global.Norm2MulVecLeErrOfMemClosureConvexHull
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.Global.EuclideanHausdorffDistAddLe

@[expose] public section

/-!
# [1, Prop. 3]: the time-interval error in the particular solution

Eq. (26)'s displayed bound: at every `t ∈ τ_k = [t_k,t_{k+1}]`, the exact `P^U(t)` sits within
`ε^U_k + Δε^{U,τ}_k(Δt_k,η_k)` of the *fixed* set `P̂^U(t_{k+1}) = P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)`
eq. (24) computes, uniformly over the whole interval. With `t = t_k + s`, `inputReach_separation_eq`
splits `P^U(t)` as `P^U(t_k) ⊕ e^{At_k}P^U(s)`, so `hausdorffDist₂_add_le` compares summand by
summand: `ε^U_k` on the accumulated one, and on the new one [1]'s own argument: since `0 ∈ U_0`,
`e^{At_k}P^U(s)` is nested increasing in `s` (`inputReach_mono`), so every exact point lies in the
closed convex hull of `P̂^U(Δt_k)` (`inputReach_subset_closure_convexHull`), and the distance to
that target is largest at `s = 0`, where the exact set is `{0}`.

## Inputs
* `sys` – linear system
* `U` – input set
* `tk` – step start time
* `Δt` – step length
* `η` – Taylor order
* `Pk` – computed set at the step start
* `εk` – error at the step start
* `t` – time

## Hypotheses
* `htk` – start time nonnegative
* `hbdd` – input set bounded
* `h0` – origin in the input set
* `hcP` – input reach at the start compact
* `hcQ` – computed set compact
* `hQne` – computed set nonempty
* `hcPs` – input reach compact over the step
* `hcQΔ` – outer one-step set compact
* `hstep` – error at the start bounds the distance
* `hconv` – input set convex
* `hclosed` – input set closed
* `hΔt` – step length positive
* `ht1` – time at least the step start
* `ht2` – time within the step

## Conclusion
* the distance at the time is at most the error plus the time-interval error

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Holding the input at the origin is admissible when `U` contains it, and contributes nothing —
`InputReachMono.lean`'s own helper of the same name, restated here since that one is file-local. -/
theorem LinearSys.aux_zero_mem_reach (sys : LinearSys 𝕋 n) {U : S n} (τ : ℝ)
    (h0 : (0 : Vec ℝ n) ∈ construct U) : (0 : Vec ℝ n) ∈ sys.inputReach U τ := by
  refine ⟨fun _ => 0, fun _ _ => h0, aestronglyMeasurable_const, ?_⟩
  simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: the error at `t_k` plus eq. (26)'s time-interval error bounds the distance, at
every `t ∈ [t_k,t_k+Δt_k]`, between the exact `P^U(t)` and the recursively computed
`P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)`. -/
theorem LinearSys.hausdorffDist₂_inputReach_tau_le (sys : LinearSys 𝕋 n) {U : S n}
    {tk Δt : ℝ} (htk : 0 ≤ tk) (η : ℕ) {Pk : Set (Vec ℝ n)} {εk : ℝ}
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U)
    (hcP : IsCompact (sys.inputReach U tk)) (hcQ : IsCompact Pk) (hQne : Pk.Nonempty)
    (hcPs : ∀ s, 0 ≤ s → s ≤ Δt → IsCompact (sys.inputReach U s))
    (hcQΔ : IsCompact (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η))
    (hstep : hausdorffDist₂ (sys.inputReach U tk) Pk ≤ εk)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U)) (hΔt : 0 < Δt)
    {t : ℝ} (ht1 : tk ≤ t) (ht2 : t ≤ tk + Δt) : -- --- CONCL ---
    hausdorffDist₂ (sys.inputReach U t)
        (Pk + (fun x => exp (tk • toRealMat sys.A) *ᵥ x)
          '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
      ≤ εk + MatExp.particularSolutionTauError
        (toRealMat sys.A) tk (construct U) Δt η := by -- --- PROOF ---
  set A := toRealMat sys.A
  set U0 := construct U
  set Y := (fun x => exp (tk • A) *ᵥ x) '' MatExp.particularSolutionOuter A U0 0 Δt η with hY
  set s := t - tk with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsΔ : s ≤ Δt := by rw [hs]; linarith
  have hcont : Continuous (fun x : Vec ℝ n => exp (tk • A) *ᵥ x) :=
    (mulVecL (exp (tk • A))).continuous
  have hcPsΔ : IsCompact (sys.inputReach U s) := hcPs s hs0 hsΔ
  have hPne : (sys.inputReach U tk).Nonempty := ⟨_, sys.aux_zero_mem_reach tk h0⟩
  have hPsne : (sys.inputReach U s).Nonempty := ⟨_, sys.aux_zero_mem_reach s h0⟩
  -- the new summand's exact set lies in the closed convex hull of the target's preimage
  have hsub : sys.inputReach U s
      ⊆ closure (convexHull ℝ (MatExp.particularSolutionOuter A U0 0 Δt η)) :=
    (sys.inputReach_mono hbdd h0 hs0 hsΔ).trans
      (sys.inputReach_subset_closure_convexHull hconv hclosed hbdd h0 hΔt η)
  have hYb : Bornology.IsBounded Y := (hcQΔ.image hcont).isBounded
  have h0Y : (0 : Vec ℝ n) ∈ Y :=
    ⟨0, MatExp.zero_mem_particularSolutionOuter A h0 0 Δt η, by simp⟩
  have hYne : Y.Nonempty := ⟨0, h0Y⟩
  -- `t = t_k + s`, split the way `Prop. 2` splits `t_{k+1} = t_k + Δt_k`
  have hsplit : sys.inputReach U t
      = sys.inputReach U tk + (fun x => exp (tk • A) *ᵥ x) '' sys.inputReach U s := by
    have ht : t = s + tk := by rw [hs]; ring
    rw [ht, sys.inputReach_separation_eq hs0 htk hbdd, add_comm]
  rw [hsplit]
  refine (hausdorffDist₂_add_le hcP hPne hcQ hQne (hcPsΔ.image hcont) (hPsne.image _)
    (hcQΔ.image hcont) hYne).trans (add_le_add hstep ?_)
  -- the distance to the fixed target `Y` peaks at `s = 0`, where the exact set is `{0}`
  refine hausdorffDist₂_le_of_mem_dist (err_nonneg Y)
    (fun x hx => ?_)
    (fun y hy => ⟨0, ⟨0, sys.aux_zero_mem_reach s h0, by simp⟩,
      by rw [sub_zero]; exact norm₂_le_err_of_mem hYb hy⟩)
  -- an exact point against `0 ∈ Y`: its norm is under `err Y`, through the closed convex hull
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨0, h0Y, ?_⟩
  rw [sub_zero]
  exact norm₂_mulVec_le_err_of_mem_closure_convexHull _ hcQΔ.isBounded (hsub hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
