module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoA
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IntersectStripGollamudiOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeAffineAdd

@[expose] public section

/-!
# The corrected `ESO-A` step encloses the true state

For positive-definite `Q` and `W`, `p ∈ (0, 1)` and `λ ∈ [0, 1)`: if the state `x` lies in the
estimate `E(Q, c)`, the disturbance `w` in `E(W, 0)` and the next state `A x + u + w` in the
measurement strip `‖C x - y‖₂ ≤ φ`, then the next state lies in `observeEsoA`. The prediction
`E((1 - p)⁻¹ A Q Aᵀ + p⁻¹ W, A c + u)` holds it (`Ellipsoid.mem_ofShape_affine_add`) and is
positive definite, so the corrected update encloses its meet with the strip
(`Ellipsoid.intersectStripGollamudi_outer`); without the update the prediction is the result.
CORA's step does not enclose it (`LinearSysDT.observeEsoA1D_counterexample`).

## Inputs
* `sys` – system
* `W` – disturbance shape
* `φ` – trigger threshold
* `p` – prediction weight
* `lam` – update weight
* `σsqPrev` – previous sigma squared
* `u` – input at this step
* `y` – measurement at this step
* `Q` – ellipsoid shape
* `c` – ellipsoid center
* `x` – state
* `w` – disturbance

## Hypotheses
* `hW` – disturbance shape positive definite
* `hp0` – prediction weight positive
* `hp1` – prediction weight below one
* `hl0` – update weight nonnegative
* `hl1` – update weight below one
* `hQ` – ellipsoid shape positive definite
* `hx` – `x` lies in the estimate
* `hw` – `w` lies in the disturbance ellipsoid
* `hy` – the next state meets the measurement strip

## Conclusion
* the next state lies in the updated ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeEsoA_outer (sys : LinearSysDT ℝ n) {W : Mat ℝ n n}
    (hW : W.PosDef) (φ : ℝ) {p lam : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (σsqPrev : ℝ) (u : Vec ℝ sys.m) (y : Vec ℝ sys.q) {Q : Mat ℝ n n}
    (hQ : Q.PosDef) (c : Vec ℝ n) {x w : Vec ℝ n} (hx : x ∈ (Ellipsoid.ofShape Q c).construct)
    (hw : w ∈ (Ellipsoid.ofShape W 0).construct)
    (hy : ‖sys.C *ᵥ (sys.A *ᵥ x + (sys.B *ᵥ u + sys.c) + w) - y‖₂ ≤ φ) : -- --- CONCL ---
    sys.A *ᵥ x + (sys.B *ᵥ u + sys.c) + w
      ∈ (sys.observeEsoA W φ p lam σsqPrev u y Q c).construct := by -- --- PROOF ---
  obtain ⟨hN, hpred⟩ :=
    Ellipsoid.mem_ofShape_affine_add hQ hW sys.A hp0 hp1 c (sys.B *ᵥ u + sys.c) hx hw
  simp only [LinearSysDT.observeEsoA]
  split_ifs
  · exact Ellipsoid.intersectStripGollamudi_outer hN _ sys.C φ y hl0 hl1 ⟨hpred, hy⟩
  · exact hpred

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
