module

public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToLinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.JointReachSetOuter
public import CORALean.ContDynamics.LinearSys.Theorems.OneStepTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.OneStepTimePointOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `linReach` holds every confined run of the DAE over the step

A run of the DAE on `[0, Δt]` from `Rinit`, confined to a region `R^z` over which `Verror`
holds the dynamics' linearization error `ℓᵈ - C F⁻¹ ℓᵃ` and `Verror_y` the constraint's `ℓᵃ`
at every consistent point, is in `linReach`'s time-point set at `Δt`, in its time-interval set
throughout, and with its algebraic variable in the joint set. Outer.

`NonlinDASys.Trajectory.toLinearSys` makes the shifted run a run of the linear system, and
`oneStep`'s two theorems do the rest; [1, Prop. 2] (`jointReachSet_outer`) places `y`. The
side conditions are `oneStep`'s: `u* ∈ U` and `0 ∈ Verror`, so that the time-varying input
holds `0`, and `F⁻¹ F = I`. Where `Verror` comes from `NonlinDASys.linError`,
`linError_outer` and `exists_lagrange_remainder` say why the certificate holds: one Lagrange
point per row and the Hessians in their intervals over `R^z`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run confined to `R^z`, over which `Verror` and `Verror_y` hold every consistent point's
errors, is in `linReach`'s time-point set at `Δt`, and its `x` and `(x, y)` in the
time-interval and joint sets throughout `[0, Δt]`. -/
theorem NonlinDASys.Trajectory.linReach_outer {sys : NonlinDASys n p m} {Δt : ℝ}
    {Rinit : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n}
    {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory (S := 𝒵) (Set.Icc 0 Δt) Rinit U x y u) (hΔt : 0 < Δt)
    {xs : Vec ℝ n} {ys : Vec ℝ p} {us : Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m}
    {C : Mat ℝ n p} {D : Mat ℝ p n} {E : Mat ℝ p m} {F F_inv : Mat ℝ p p}
    (hF : F_inv * F = 1) {Verror : Zonotope (Vec ℝ n)} {Verror_y : Zonotope (Vec ℝ p)}
    {Rz : Set (Vec ℝ n × Vec ℝ p × Vec ℝ m)} (hR : ∀ t ∈ Set.Icc 0 Δt, (x t, y t, u t) ∈ Rz)
    (hL : ∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      (sys.f x' y' u' - (sys.f xs ys us + A *ᵥ (x' - xs) + B *ᵥ (u' - us) + C *ᵥ (y' - ys)))
        - (C * F_inv) *ᵥ (sys.g x' y' u' - (sys.g xs ys us + D *ᵥ (x' - xs) + E *ᵥ (u' - us)
          + F *ᵥ (y' - ys))) ∈ Verror.construct)
    (hLa : ∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      sys.g x' y' u' - (sys.g xs ys us + D *ᵥ (x' - xs) + E *ᵥ (u' - us) + F *ᵥ (y' - ys))
        ∈ Verror_y.construct)
    (hus : us ∈ U.construct) (h0 : (0 : Vec ℝ n) ∈ Verror.construct) {q : ℕ}
    (hε : ‖Δt • (A - C * F_inv * D)‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1) :
    let R := NonlinDASys.linReach (sys.f xs ys us) (sys.g xs ys us) A B C D E F_inv xs ys us
      Rinit U Verror Verror_y Δt (q + 2)
    x Δt ∈ R.1.construct ∧
      ∀ t ∈ Set.Icc 0 Δt,
        x t ∈ R.2.1.construct ∧ (x t, y t) ∈ R.2.2.construct := by -- --- PROOF ---
  intro R
  set A_lin : Mat ℝ n n := A - C * F_inv * D with hA_lin
  set f0 : Vec ℝ n := sys.f xs ys us - (C * F_inv) *ᵥ sys.g xs ys us with hf0
  set U_lin : Zonotope (Vec ℝ n) := (U.plus (Zonotope.ofPoint (-us))).mtimes (B - C * F_inv * E)
    with hU_lin
  set W : Zonotope (Vec ℝ n) := (Zonotope.ofPoint f0).plus (U_lin.plus Verror) with hW
  -- the shifted run is a run of the linear system `oneStep` is taken of
  have lin := (traj.toLinearSys hF hR hL).trajectory (convex_Icc 0 Δt) ⟨le_rfl, hΔt.le⟩
    (Zonotope.isBounded_construct _)
  -- `oneStep`'s side conditions, all of zonotopes
  have hWU : ∀ v ∈ construct (S := Zonotope (Vec ℝ n)) W,
      v - f0 ∈ construct (S := Zonotope (Vec ℝ n)) (U_lin.plus Verror) := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := (Zonotope.plus_exact _ _).symm.subset hv
    rw [(Zonotope.mem_ofPoint_iff _ _).mp ha, add_sub_cancel_left]
    exact hb
  have h0U : (0 : Vec ℝ n) ∈ construct (S := Zonotope (Vec ℝ n)) (U_lin.plus Verror) := by
    show (0 : Vec ℝ n) ∈ (U_lin.plus Verror).construct
    rw [← Zonotope.plus_exact, ← zero_add (0 : Vec ℝ n)]
    refine Set.add_mem_add ?_ h0
    rw [hU_lin, ← Zonotope.mtimes_exact, ← Zonotope.plus_exact]
    exact ⟨us + -us, Set.add_mem_add hus (Zonotope.mem_ofPoint _), by simp⟩
  have hε' : ‖Δt • Scalar.toRealMat (LinearSys.canonical A_lin : LinearSys ℝ n).A‖ /
      (((q + 2 : ℕ) : ℝ) + 2) < 1 := by
    rw [Scalar.toRealMat_real]; exact hε
  -- the time-varying input's interval-matrix images, and `{f0}`, are zonotopes too
  have hRc := Zonotope.convex_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (U_lin.plus Verror))
  have hRk := Zonotope.isClosed_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (U_lin.plus Verror))
  have hRb := Zonotope.isBounded_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (U_lin.plus Verror))
  have pRc := Zonotope.convex_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (Zonotope.ofPoint f0))
  have pRk := Zonotope.isClosed_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (Zonotope.ofPoint f0))
  have pRb := Zonotope.isBounded_construct (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
    (MatExp.inputRemainder A_lin Δt (q + 2)) (Zonotope.ofPoint f0))
  -- moving a shifted set back by `x*`
  have hback : ∀ (Z : Zonotope (Vec ℝ n)) (v : Vec ℝ n), v - xs ∈ Z.construct →
      v ∈ (Z.plus (Zonotope.ofPoint xs)).construct := by
    intro Z v hv
    rw [← Zonotope.plus_exact]
    exact ⟨v - xs, hv, xs, Zonotope.mem_ofPoint _, sub_add_cancel v xs⟩
  have hti : ∀ t ∈ Set.Icc 0 Δt, x t ∈ R.2.1.construct := by
    intro t ht
    exact hback _ _ (lin.oneStep_timeInterval_outer hΔt hε' h0U ht.1 ht.2 hWU
      (Zonotope.isBounded_construct _) (Zonotope.convex_construct _)
      (Zonotope.isClosed_construct _) (Zonotope.isBounded_construct _) hRc hRk hRb
      (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
      (Zonotope.isBounded_construct _) pRc pRk pRb)
  refine ⟨hback _ _ (lin.oneStep_timePoint_outer hΔt hε' hWU (Zonotope.isBounded_construct _)
      (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
      (Zonotope.isBounded_construct _) hRc hRk hRb (Zonotope.convex_construct _)
      (Zonotope.isClosed_construct _) (Zonotope.isBounded_construct _) pRc pRk pRb),
    fun t ht => ⟨hti t ht, ?_⟩⟩
  -- [1, Prop. 2]: the algebraic variable from the linearized constraint and its error
  have hg := traj.constraint t ht
  refine NonlinDASys.jointReachSet_outer hF (hti t ht) (traj.input t ht)
    (hLa _ _ _ (hR t ht) hg) ?_
  rw [hg]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
