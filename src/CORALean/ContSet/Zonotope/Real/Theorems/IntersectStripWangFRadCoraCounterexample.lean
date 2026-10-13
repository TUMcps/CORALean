import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
import CORALean.ContSet.Zonotope.Real.Definitions.FWRadius

/-!
# CORA's `'wang-FRad'` gain is not the F-radius minimizer

CORA's `@zonotope/intersectStrip` with `'wang-FRad'` (`aux_methodWangFRad`, used by the observer
`FRad-B`) cites [1, Thm. 2] and computes `R̄ = A P Aᵀ + Q_w`, `P = G Gᵀ`, `λ = R̄ Cᵀ (C R̄ Cᵀ +
Q_v)⁻¹` from the generators `G` of the zonotope it intersects. But `observe_stripBased` calls it on
the *predicted* set `A X̂ ⊕ W`, whose Gram matrix already is the paper's `R̄` (at `T = I`, `N = 0`);
CORA applies `A` and adds `Q_w` a second time. In one dimension, the predicted zonotope `⟨0, [1]⟩`,
`C = 1`, `φ = 1` (`Q_v = 1`), `A = 2` and no disturbance give CORA's gain `λ = 4·1/(4 + 1) = 4/5`,
while [1, Thm. 2] gives `1/(1 + 1) = 1/2`. The F-radius of the result, `√((1 - λ)² + λ²)`, is
`√(17/25)` at CORA's gain and `√(1/2)` at the paper's, so CORA's is strictly worse. The enclosure is
unaffected: every gain is sound (`intersectStrip_outer`).

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectStrip_wangFRadCora_counterexample :
    let Z : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩      -- the predicted set, `P = 1`
    let a : ℝ := 2                                          -- `A`
    let lamCora : ℝ := (a * 1 * a + 0) * 1 / (1 * (a * 1 * a + 0) * 1 + 1)   -- CORA
    let lamWang : ℝ := 1 * 1 / (1 * 1 * 1 + 1)                               -- [1, Thm. 2]
    let strip := fun lam : ℝ => Z.intersectStrip (fun _ _ => 1 : Mat ℝ 1 1) (fun _ => 1 : Vec ℝ 1)
      (fun _ => 0 : Vec ℝ 1) (fun _ _ => lam : Mat ℝ 1 1)
    (strip lamWang).fwRadius 1 < (strip lamCora).fwRadius 1 := by -- --- PROOF ---
  intro Z a lamCora lamWang strip
  -- the squared F-radius at a gain `lam` is `(1 - lam)² + lam²`
  have hJ : ∀ lam : ℝ, ∑ j, (strip lam).G j ⬝ᵥ ((1 : Mat ℝ 1 1) *ᵥ (strip lam).G j) =
      (1 - lam) ^ 2 + lam ^ 2 := fun lam => by
    show ∑ j : Fin (1 + 1), _ = _
    rw [Fin.sum_univ_add]
    have hlast : ∀ f g : Fin 1 → Vec ℝ 1, Fin.append f g (1 : Fin (1 + 1)) = g 0 := fun f g => by
      simp [Fin.append, Fin.addCases, Fin.subNat]
    simp only [strip, Zonotope.intersectStrip, Fin.append_left]
    simp [Z, Matrix.mul_apply, Matrix.mulVec, dotProduct, hlast]
    ring
  simp only [Zonotope.fwRadius, hJ]
  exact Real.sqrt_lt_sqrt (by positivity) (by norm_num [lamCora, lamWang, a])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
