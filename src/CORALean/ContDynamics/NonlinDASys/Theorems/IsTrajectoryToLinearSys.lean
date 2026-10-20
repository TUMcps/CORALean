module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.NonlinDASys.Theorems.MemLinInclusion
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A confined run of the DAE is a run of the linear system `linReach` steps

[1, Prop. 1] read for the deviation `x̃ = x - x*`: a run of the DAE that stays in a region `R^z`
over which `Verror` holds every consistent point's linearization error `ℓᵈ - C F⁻¹ ℓᵃ` is,
shifted by `-x*`, a run of `˙x̃ = Ã x̃ + v` from `Rinit - x*` with the input
`v(t) = f(z(t)) - Ã x̃(t)` in `w ⊕ B̃ (U ⊕ (-u*)) ⊕ Verror`, the linear system
`NonlinDASys.linReach` hands to `oneStep`. The input lies there by `NonlinDASys.mem_linInclusion`,
which uses only `F⁻¹ F = I`. The confinement and the error certificate are hypotheses, as in
`NonlinDASys.IsTrajectory.field_mem_linInclusion`: CORA checks the error after the fact on a set
computed under the assumption it checks.

## Inputs
* `sys` – system
* `T` – time set
* `Rinit` – initial zonotope
* `U` – input zonotope
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal
* `xs` – linearization state
* `ys` – linearization algebraic variable
* `us` – linearization input
* `A` – dynamics Jacobian in the state
* `B` – dynamics Jacobian in the input
* `C` – dynamics Jacobian in the algebraic variable
* `D` – constraint Jacobian in the state
* `E` – constraint Jacobian in the input
* `F` – constraint Jacobian in the algebraic variable
* `F_inv` – inverse of `F`
* `Verror` – dynamics error zonotope
* `Rz` – confinement region

## Hypotheses
* `traj` – DAE trajectory
* `hF` – `F_inv` is a left inverse of `F`
* `hTm` – time set measurable
* `hR` – the run stays in the region
* `hL` – `Verror` holds every consistent point's error

## Conclusion
* the shifted run solves the linear system with the bounded input

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet
open scoped Pointwise

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: a run confined to `R^z`, over which `Verror` holds every consistent point's
linearization error, is shifted by `-x*` a run of `Ã x̃ ⊕ w ⊕ B̃ (U ⊕ (-u*)) ⊕ Verror`. -/
theorem NonlinDASys.IsTrajectory.toLinearSys {sys : NonlinDASys n p m} {T : Set ℝ}
    {Rinit : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n}
    {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m} {z : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := 𝒵) T Rinit U x y u z)
    {xs : Vec ℝ n} {ys : Vec ℝ p} {us : Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m}
    {C : Mat ℝ n p} {D : Mat ℝ p n} {E : Mat ℝ p m} {F F_inv : Mat ℝ p p}
    (hF : F_inv * F = 1) (hTm : MeasurableSet T) {Verror : Zonotope (Vec ℝ n)}
    {Rz : Set (Vec ℝ n × Vec ℝ p × Vec ℝ m)} (hR : ∀ t ∈ T, (x t, y t, u t) ∈ Rz)
    (hL : ∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      (sys.f x' y' u' - (sys.f xs ys us + A *ᵥ (x' - xs) + B *ᵥ (u' - us) + C *ᵥ (y' - ys)))
        - (C * F_inv) *ᵥ (sys.g x' y' u' - (sys.g xs ys us + D *ᵥ (x' - xs) + E *ᵥ (u' - us)
          + F *ᵥ (y' - ys))) ∈ Verror.construct) :
    (LinearSys.canonical (A - C * F_inv * D) : LinearSys ℝ n).IsCanonicalTrajectory
        (S := 𝒵) T
      (Rinit.plus (Zonotope.ofPoint (-xs)))
      ((Zonotope.ofPoint (sys.f xs ys us - (C * F_inv) *ᵥ sys.g xs ys us)).plus
        (((U.plus (Zonotope.ofPoint (-us))).mtimes (B - C * F_inv * E)).plus Verror))
      (fun t => x t - xs)
      (fun t => sys.f (x t) (y t) (u t) - (A - C * F_inv * D) *ᵥ (x t - xs)) where
  init := by
    show x 0 - xs ∈ (Rinit.plus (Zonotope.ofPoint (-xs))).construct
    rw [← Zonotope.plus_exact, sub_eq_add_neg]
    exact Set.add_mem_add traj.init (Zonotope.mem_ofPoint _)
  input t ht := by
    -- [1, Eq. 16]: the field is `Ã Δx` plus a point of `Ũ`
    obtain ⟨_, rfl, v, ⟨_, ⟨w, rfl, b, ⟨_, ⟨u', hu', rfl⟩, rfl⟩, rfl⟩, l, hl, rfl⟩, hsum⟩ :=
      NonlinDASys.mem_linInclusion sys (U := U.construct) (L := Verror.construct) hF
        (traj.input t ht) (traj.constraint t ht)
        (hL _ _ _ (hR t ht) (traj.constraint t ht))
    show sys.f (x t) (y t) (u t) - (A - C * F_inv * D) *ᵥ (x t - xs) ∈
      ((Zonotope.ofPoint (sys.f xs ys us - (C * F_inv) *ᵥ sys.g xs ys us)).plus
        (((U.plus (Zonotope.ofPoint (-us))).mtimes (B - C * F_inv * E)).plus Verror)).construct
    rw [← hsum, add_sub_cancel_left]
    rw [← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.mtimes_exact,
      ← Zonotope.plus_exact]
    beta_reduce
    rw [add_assoc]
    refine Set.add_mem_add (Zonotope.mem_ofPoint _) (Set.add_mem_add ⟨u' - us, ?_, rfl⟩ hl)
    rw [sub_eq_add_neg]
    exact Set.add_mem_add hu' (Zonotope.mem_ofPoint _)
  -- the shifted input is the field less a continuous drift, so measurable
  meas := traj.meas.sub (((mulVecL (A - C * F_inv * D)).continuous.comp_continuousOn
    (traj.cont.sub continuousOn_const)).aestronglyMeasurable hTm)
  cont := traj.cont.sub continuousOn_const
  flow t ht := by
    -- the field at the shifted state is the DAE's field, the run's integrand
    have he : (fun s => Scalar.toRealMat (A - C * F_inv * D) *ᵥ (x s - xs)
        + (sys.f (x s) (y s) (u s) - (A - C * F_inv * D) *ᵥ (x s - xs)))
          = fun s => sys.f (x s) (y s) (u s) := by
      funext s; rw [Scalar.toRealMat_real]; abel
    show x t - xs = (x 0 - xs) + ∫ s in (0:ℝ)..t, (Scalar.toRealMat (A - C * F_inv * D)
      *ᵥ (x s - xs) + (sys.f (x s) (y s) (u s) - (A - C * F_inv * D) *ᵥ (x s - xs)))
    rw [he, traj.flow t ht]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
