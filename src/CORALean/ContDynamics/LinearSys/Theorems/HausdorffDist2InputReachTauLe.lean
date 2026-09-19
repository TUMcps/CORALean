import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionTauError
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.Global.EuclideanHausdorffDistAddLe

/-!
# [1, Prop. 3]: the time-interval error in the particular solution

Eq. (26)'s displayed bound: at every `t ∈ τ_k = [t_k,t_{k+1}]`, the exact `P^U(t)` sits within
`ε^U_k + Δε^{U,τ}_k(Δt_k,η_k)` of the *fixed* set `P̂^U(t_{k+1}) = P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)`
eq. (24) recursively computes — the same target `Prop. 2` bounds only at `t = t_{k+1}` itself, now
bounded uniformly over the whole interval.

Writing `t = t_k + s` with `s ∈ [0,Δt_k]`, `inputReach_separation_eq` splits `P^U(t)` the same way
`Prop. 2` splits `P^U(t_{k+1})`: `P^U(t_k) ⊕ e^{At_k}P^U(s)`, so `hausdorffDist₂_add_le` again
compares summand by summand — `ε^U_k` on the accumulated one, and on the new one, `[1]`'s own
argument: since `0 ∈ U_0`, `e^{At_k}P^U(s)` is nested increasing in `s` (`inputReach_mono`,
Althoff's `Prop. 3.3`, `0 ∈ U_0` is exactly what it asks for) and contained in the fixed target
`e^{At_k}P̂^U(Δt_k)` throughout, so the Hausdorff distance to that fixed target is largest at
`s = 0`, where the exact set is `{0}` — `d_H(0,e^{At_k}P̂^U(Δt_k)) ≤ err(e^{At_k}P̂^U(Δt_k)) =:
Δε^{U,τ}_k(Δt_k,η_k)`, `[1]`'s eq. (12) read off a single witness on each side rather than
[1]'s own monotonicity-of-`d_H` argument.

Compactness of the sets is what `Def. 5` asks of everything it measures, exactly as for `Prop. 2`.

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

-- eight set-valued arguments to `hausdorffDist₂_add_le`, each re-solving the matrix instances
set_option maxHeartbeats 400000 in
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
    (houter : sys.inputReach U Δt
      ⊆ MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
    {t : ℝ} (ht1 : tk ≤ t) (ht2 : t ≤ tk + Δt) :
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
  -- the new summand's exact set is nested inside the fixed target `Y` throughout `[0,Δt]`
  have hsub : sys.inputReach U s ⊆ MatExp.particularSolutionOuter A U0 0 Δt η :=
    (sys.inputReach_mono hbdd h0 hs0 hsΔ).trans houter
  have hXsubY : (fun x => exp (tk • A) *ᵥ x) '' sys.inputReach U s ⊆ Y := Set.image_mono hsub
  have hYb : Bornology.IsBounded Y := (hcQΔ.image hcont).isBounded
  have hYne : Y.Nonempty := (hPsne.image _).mono hXsubY
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
    (fun x hx => ⟨x, hXsubY hx, by rw [sub_self, norm₂_zero]; exact err_nonneg Y⟩)
    (fun y hy => ⟨0, ⟨0, sys.aux_zero_mem_reach s h0, by simp⟩,
      by rw [sub_zero]; exact norm₂_le_err_of_mem hYb hy⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
