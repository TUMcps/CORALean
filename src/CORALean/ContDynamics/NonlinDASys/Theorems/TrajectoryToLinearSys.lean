module

public import CORALean.ContDynamics.LinearSys.Definitions.CanonicalClassicalTrajectory
public import CORALean.ContDynamics.NonlinDASys.Theorems.MemLinInclusion
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import Mathlib.Analysis.Calculus.Deriv.Add
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A confined run of the DAE is a run of the linear system `linReach` steps

[1, Prop. 1] read for the deviation `x̃ = x - x*`: a run of the DAE that stays in a region
`R^z` over which `Verror` holds every consistent point's linearization error
`ℓᵈ - C F⁻¹ ℓᵃ` is, shifted by `-x*`, a run of `˙x̃ = Ã x̃ + v` from `Rinit - x*` with the
input `v(t) = f(z(t)) - Ã x̃(t)` in `w ⊕ B̃ (U ⊕ (-u*)) ⊕ Verror`, all as zonotopes, the
linear system `NonlinDASys.linReach` hands to `oneStep`. The input lies there by
`NonlinDASys.mem_linInclusion`, which uses only `F⁻¹ F = I`.

The confinement and the error certificate are hypotheses, as in
`NonlinDASys.Trajectory.hasDerivWithinAt_mem_linInclusion`: CORA checks the error after
the fact on a set computed under the assumption it checks.

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
open scoped Pointwise

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: a run confined to `R^z`, over which `Verror` holds every consistent point's
linearization error, is shifted by `-x*` a run of `Ã x̃ ⊕ w ⊕ B̃ (U ⊕ (-u*)) ⊕ Verror`. -/
theorem NonlinDASys.Trajectory.toLinearSys {sys : NonlinDASys n p m} {T : Set ℝ}
    {Rinit : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n}
    {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m} (traj : sys.Trajectory (S := 𝒵) T Rinit U x y u)
    {xs : Vec ℝ n} {ys : Vec ℝ p} {us : Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m}
    {C : Mat ℝ n p} {D : Mat ℝ p n} {E : Mat ℝ p m} {F F_inv : Mat ℝ p p}
    (hF : F_inv * F = 1) {Verror : Zonotope (Vec ℝ n)}
    {Rz : Set (Vec ℝ n × Vec ℝ p × Vec ℝ m)} (hR : ∀ t ∈ T, (x t, y t, u t) ∈ Rz)
    (hL : ∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      (sys.f x' y' u' - (sys.f xs ys us + A *ᵥ (x' - xs) + B *ᵥ (u' - us) + C *ᵥ (y' - ys)))
        - (C * F_inv) *ᵥ (sys.g x' y' u' - (sys.g xs ys us + D *ᵥ (x' - xs) + E *ᵥ (u' - us)
          + F *ᵥ (y' - ys))) ∈ Verror.construct) :
    (LinearSys.canonical (A - C * F_inv * D) : LinearSys ℝ n).CanonicalClassicalTrajectory (S := 𝒵)
        T
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
  flow t ht := by
    -- the field at the shifted state is the DAE's field, which is the run's derivative
    have he : Scalar.toRealMat (A - C * F_inv * D) *ᵥ (x t - xs)
        + (sys.f (x t) (y t) (u t) - (A - C * F_inv * D) *ᵥ (x t - xs))
          = sys.f (x t) (y t) (u t) := by
      rw [Scalar.toRealMat_real]; abel
    show HasDerivWithinAt (fun t => x t - xs) (Scalar.toRealMat (A - C * F_inv * D)
      *ᵥ (x t - xs) + (sys.f (x t) (y t) (u t) - (A - C * F_inv * D) *ᵥ (x t - xs))) T t
    rw [he]
    exact (hasDerivWithinAt_sub_const_iff xs).mpr (traj.flow t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
