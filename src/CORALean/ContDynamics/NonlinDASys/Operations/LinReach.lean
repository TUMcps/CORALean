module

public import CORALean.ContDynamics.NonlinDASys.Operations.JointReachSet
public import CORALean.ContDynamics.LinearSys.Operations.OneStep
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `NonlinDASys.linReach`

CORA's `nonlinDASys/linReach` for one step, one `let` per CORA variable: `priv_linearize`
builds the linear system `Ã x̃ ⊕ w ⊕ B̃ (U ⊕ (-u*))` of [1, Eq. 14], [1, Eq. 16] at the
expansion point `z* = (x*, y*, u*)`, `oneStep` runs it from `Rinit - x*`, the sets are moved
back by `x*`, and the algebraic set is [1, Prop. 2]'s `jointReachSet` over the time-interval
set. The Jacobian blocks, `F⁻¹`, `f(z*)`, `g(z*)` and the error sets are data.

Departures from CORA, on purpose. The error sets `Verror` (the dynamics', `ℓᵈ - C F⁻¹ ℓᵃ`)
and `Verror_y` (the constraint's, `ℓᵃ`) are arguments: CORA's `priv_linError_mixed_noInt` adds
`CF_inv` times the algebraic error where [1, Cor. 1] subtracts it (FINDINGS.md), and
`NonlinDASys.linError` is the corrected set. The `while` loop that grows the assumed error
until it covers the computed one becomes the region the theorem confines the run to.
`Verror` joins the time-varying input of `oneStep`, where CORA adds
`particularSolution_timeVarying(Verror)` to both sets afterwards; the algebraic set is the
second component of the joint set, which CORA builds as `R_xy` and projects.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `linReach` for a DAE, at the error sets `Verror` and `Verror_y`:
the time-point set, the time-interval set, and the joint set of `(x, y)` over the step. -/
noncomputable def NonlinDASys.linReach (f₀ : Vec ℝ n) (g₀ : Vec ℝ p) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (C : Mat ℝ n p) (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p)
    (xs : Vec ℝ n) (ys : Vec ℝ p) (us : Vec ℝ m) (Rinit : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (Verror : Zonotope (Vec ℝ n)) (Verror_y : Zonotope (Vec ℝ p))
    (Δt : ℝ) (η : ℕ) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n × Vec ℝ p) :=
  let CF_inv : Mat ℝ n p := C * F_inv                                     -- CF_inv
  let f0 : Vec ℝ n := f₀ - CF_inv *ᵥ g₀                                  -- linParams.uTrans
  let A_lin : Mat ℝ n n := A - CF_inv * D                                 -- A_lin
  let B_lin : Mat ℝ n m := B - CF_inv * E                                 -- B_lin
  let linsys : LinearSys ℝ n := LinearSys.canonical A_lin  -- linearSys(A_lin, 1)
  let U_lin : Zonotope (Vec ℝ n) :=                                       -- B_lin (U - p.u)
    (U.plus (Zonotope.ofPoint (-us))).mtimes B_lin
  let Rdelta : Zonotope (Vec ℝ n) := Rinit.plus (Zonotope.ofPoint (-xs))  -- Rinit - p.x
  let R := linsys.oneStep (S := 𝒵) Rdelta (U_lin.plus Verror) f0 Δt η    -- oneStep
  let Rtp : Zonotope (Vec ℝ n) := R.Rtp.plus (Zonotope.ofPoint xs)          -- Rtp + p.x
  let Rti : Zonotope (Vec ℝ n) := R.Rti.plus (Zonotope.ofPoint xs)          -- Rti + p.x
  let Rti_y := NonlinDASys.jointReachSet xs ys us g₀ D E F_inv Rti U Verror_y   -- R_xy
  (Rtp, Rti, Rti_y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
