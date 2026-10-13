module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveEsoB
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IntersectStripLiuOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeAffineAdd

@[expose] public section

/-!
# The corrected `ESO-B` step encloses the true state

For positive-definite `Q`, `W` and `V`, `p ∈ (0, 1)` and `λ ∈ (0, 1)`: if the state `x` lies
in the estimate `E(Q, c)`, the disturbance `w` in `E(W, 0)` and the next state `x' = A x + u + w`
has `(y - C x')ᵀ V⁻¹ (y - C x') ≤ 1` (the measurement noise in `E(0, V)`), then `x'` lies in
`observeEsoB`. The prediction `E((1 - p)⁻¹ A Q Aᵀ + p⁻¹ W, A c + u)` holds it
(`Ellipsoid.mem_ofShape_affine_add`), which is its level-`1` set, so the corrected update at
`σ²_prev = 1` encloses its meet with the measurement set (`Ellipsoid.intersectStripLiu_outer`);
without the update the prediction is the result. CORA's step does not enclose it
(`LinearSysDT.observeEsoB1D_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeEsoB_outer (sys : LinearSysDT ℝ n) (C : Mat ℝ m n) {W : Mat ℝ n n}
    (hW : W.PosDef) {V : Mat ℝ m m} (hV : V.PosDef) {p lam : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hl0 : 0 < lam) (hl1 : lam < 1) (σsqPrev : ℝ) (u : Vec ℝ n) (y : Vec ℝ m) {Q : Mat ℝ n n}
    (hQ : Q.PosDef) (c : Vec ℝ n) {x w : Vec ℝ n} (hx : x ∈ (Ellipsoid.ofShape Q c).construct)
    (hw : w ∈ (Ellipsoid.ofShape W 0).construct)
    (hy : (y - C *ᵥ (sys.A *ᵥ x + u + w)) ⬝ᵥ V⁻¹ *ᵥ (y - C *ᵥ (sys.A *ᵥ x + u + w)) ≤ 1) :
    sys.A *ᵥ x + u + w
      ∈ (sys.observeEsoB C W V p lam σsqPrev u y Q c).construct := by -- --- PROOF ---
  obtain ⟨hN, hpred⟩ := Ellipsoid.mem_ofShape_affine_add hQ hW sys.A hp0 hp1 c u hx hw
  simp only [LinearSysDT.observeEsoB]
  split_ifs
  · rw [Ellipsoid.mem_ofShape_iff hN] at hpred
    exact Ellipsoid.intersectStripLiu_outer hN _ C hV y 1 hl0 hl1 ⟨hpred, hy⟩
  · exact hpred

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
