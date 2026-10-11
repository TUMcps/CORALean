import CORALean.ContDynamics.LinearSys.Operations.OneStep
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachShift

/-!
# `oneStep` holds the state at every time of the step

`Rti` of `LinearSys.oneStep` [1, Sec. 3.3] encloses `x(t)` for every `t ∈ [0, Δt]` of every
run from `X` whose input is the constant `u` plus a signal in `U ∋ 0`. The state is
`e^{At} x₀ + Γ(t) u + p`, and with `λ = t/Δt` it comes apart into
`(1-λ) x₀ + λ (e^{AΔt} x₀ + Γ(Δt) u)`, a point of the hull of `X` and `Htp`,
`F x₀` with the state's interpolation error `[F]`, `G u` with the constant's `[G]`, and `p`,
a `U`-input's contribution up to `t`, which `0 ∈ U` lifts to `Δt` (`inputReach_mono`) and
`PU` holds.

Outer only: the hull is a `linComb`, and `Pu`, `PU`, `F`, `G` are bounds.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at every time of the step is in `oneStep`'s time-interval set. -/
theorem LinearSys.Trajectory.oneStep_timeInterval_outer {sys : LinearSys 𝕋 n} {Δt : ℝ}
    (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {X U W : S n}
    {x w : ℝ → Vec ℝ n} {u : Vec ℝ n}
    (traj : sys.Trajectory (Set.Icc 0 Δt) X W x w) (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htΔ : t ≤ Δt)
    (hWU : ∀ v ∈ construct W, v - u ∈ construct U) (hW : Bornology.IsBounded (construct W))
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) U)))
    (pconv : Convex ℝ (construct (OfPoint.ofPoint (S := S n) u)))
    (pclosed : IsClosed (construct (OfPoint.ofPoint (S := S n) u)))
    (pbdd : Bornology.IsBounded (construct (OfPoint.ofPoint (S := S n) u)))
    (pRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u))))
    (pRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u))))
    (pRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt (m + 2)) (OfPoint.ofPoint (S := S n) u)))) :
    x t ∈ construct (sys.oneStep X U u Δt (m + 2)).2 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set lam : ℝ := t / Δt with hlam
  have hl0 : 0 ≤ lam := div_nonneg ht0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr htΔ
  have hp := traj.sub_mem_inputReach_shift u hWU hW hbdd ⟨ht0, htΔ⟩
  have hPU := sys.inputReach_subset_inputSolution hΔt (m + 2) hε hconv hclosed hbdd hRconv
    hRclosed hRbdd (sys.inputReach_mono hbdd h0 ht0 htΔ hp)
  have hPu := sys.inputReach_subset_inputSolution (U := (OfPoint.ofPoint u : S n)) hΔt (m + 2)
    hε pconv pclosed pbdd pRconv pRclosed pRbdd
    ⟨fun _ => u, fun _ _ => OfPoint.mem_ofPoint u, aestronglyMeasurable_const,
      (MatExp.expIntegral_constInput A u hΔt.le).symm⟩
  have hex : exp (Δt • A) *ᵥ x 0 ∈ construct (Mtimes.mtimes (exp (Δt • A)) X) :=
    Mtimes.mtimes_outer _ X (Set.mem_iUnion₂.mpr ⟨_, rfl, Set.mem_image_of_mem _ traj.init⟩)
  -- the hull of `X` and `Htp` holds the interpolated point
  have hHtp : exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u
      ∈ construct (Plus.plus (Mtimes.mtimes (exp (Δt • A)) X)
        (sys.inputSolution Δt (m + 2) (OfPoint.ofPoint u : S n))) :=
    Plus.plus_outer _ _ (Set.add_mem_add hex hPu)
  have hlin := LinComb.linComb_outer X (Plus.plus (Mtimes.mtimes (exp (Δt • A)) X)
    (sys.inputSolution Δt (m + 2) (OfPoint.ofPoint u : S n)))
    ⟨x 0, traj.init, _, hHtp, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- the two interpolation errors
  have hF : (exp (t • A) - 1 - lam • (exp (Δt • A) - 1)) *ᵥ x 0
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix A Δt (m + 2)) X) :=
    Mtimes.mtimes_outer (𝕄 := ℐ) _ X (Set.mem_biUnion
      (MatExp.expDiff_mem_correctionMatrix A hΔt hε ht0 htΔ) (Set.mem_image_of_mem _ traj.init))
  have hG : (MatExp.expIntegral A t - lam • MatExp.expIntegral A Δt) *ᵥ u
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrix A Δt (m + 2))
        (OfPoint.ofPoint (S := S n) u)) :=
    Mtimes.mtimes_outer (𝕄 := ℐ) _ _ (Set.mem_biUnion
      (MatExp.expIntegralDiff_mem_constCorrectionMatrix A hΔt (m + 2) hε ht0 htΔ)
      (Set.mem_image_of_mem _ (OfPoint.mem_ofPoint u)))
  -- the state is the interpolated point, the two errors, and the input's share
  have hx : x t = ((((1 - lam) • x 0 + lam • (exp (Δt • A) *ᵥ x 0 + MatExp.expIntegral A Δt *ᵥ u))
      + (exp (t • A) - 1 - lam • (exp (Δt • A) - 1)) *ᵥ x 0)
      + (x t - (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ u)))
      + (MatExp.expIntegral A t - lam • MatExp.expIntegral A Δt) *ᵥ u := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul,
      smul_add]
    abel
  -- the four parts, regrouped into `((Hti ⊞ PU) ⊞ C_input)`
  show x t ∈ construct (Plus.plus (Plus.plus _ _) _)
  rw [hx]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add hlin hF)) hPU)) hG)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
