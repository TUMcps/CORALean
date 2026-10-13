import CORALean.ContSet.Zonotope.Real.Theorems.CrossSupport
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# A point of an edge is not interior

The zonogon is on one side of the line of an edge (`cross_support`), so a point of the edge cannot
have a ball in the zonogon: the point a little way across the line is not in it. This is the half
of [1, Alg. 3]'s boundary description that says the edges are on the boundary, for an edge with a
nonzero generator.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.edge_not_mem_interior (Z : Zonotope (Vec ℝ 2)) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (s : Fin Z.h → Bool) (a : Fin Z.h) (ha : s a = false)
    (hB : ∀ b, s b = true → 0 ≤ σ * (Z.G b 0 * Z.G a 1 - Z.G b 1 * Z.G a 0))
    (hC : ∀ c, s c = false → c ≠ a → 0 ≤ σ * (Z.G a 0 * Z.G c 1 - Z.G a 1 * Z.G c 0))
    (hga : Z.G a ≠ 0) {x : Vec ℝ 2}
    (hx : x ∈ segment ℝ (Z.corner s) (Z.corner s + (2 : ℝ) • Z.G a)) :
    x ∉ interior Z.construct := by -- --- PROOF ---
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- the point `x` is `P + t (2 g_a)` on the edge
  rw [segment_eq_image'] at hx
  obtain ⟨t, -, hxt⟩ := hx
  have hx0 : x 0 = Z.corner s 0 + t * (2 * Z.G a 0) := by
    rw [← hxt]; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hx1 : x 1 = Z.corner s 1 + t * (2 * Z.G a 1) := by
    rw [← hxt]; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  -- a point across the edge's line, within the ball
  have hgpos : 0 < |Z.G a 0| + |Z.G a 1| := by
    by_contra h
    apply hga
    have h0 : |Z.G a 0| = 0 := le_antisymm (by linarith [abs_nonneg (Z.G a 1)]) (abs_nonneg _)
    have h1 : |Z.G a 1| = 0 := le_antisymm (by linarith [abs_nonneg (Z.G a 0)]) (abs_nonneg _)
    ext k; fin_cases k
    · exact abs_eq_zero.mp h0
    · exact abs_eq_zero.mp h1
  -- `ρ` is half the radius over the size of `g_a`
  set ρ : ℝ := ε / (2 * (|Z.G a 0| + |Z.G a 1|)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρle : ρ * (|Z.G a 0| + |Z.G a 1|) < ε := by
    rw [hρ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hz : (![x 0 + ρ * σ * Z.G a 1, x 1 - ρ * σ * Z.G a 0] : Vec ℝ 2) ∈ Z.construct := by
    refine hball ((dist_pi_lt_iff hε).mpr fun k => ?_)
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    fin_cases k
    · show dist (x 0 + ρ * σ * Z.G a 1) (x 0) < ε
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_mul, abs_of_pos hρpos, hσabs, mul_one]
      nlinarith [mul_nonneg hρpos.le (abs_nonneg (Z.G a 0))]
    · show dist (x 1 - ρ * σ * Z.G a 0) (x 1) < ε
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_mul, abs_mul, abs_of_pos hρpos, hσabs,
        mul_one]
      nlinarith [mul_nonneg hρpos.le (abs_nonneg (Z.G a 1))]
  -- but the zonogon is on one side of the edge's line
  have hsup := Z.cross_support σ s a ha hB hC hz
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hsup
  rw [hx0, hx1] at hsup
  have hsq : 0 < Z.G a 0 ^ 2 + Z.G a 1 ^ 2 := by
    have h1 : (|Z.G a 0| + |Z.G a 1|) ^ 2 ≤ 2 * (Z.G a 0 ^ 2 + Z.G a 1 ^ 2) := by
      nlinarith [sq_abs (Z.G a 0), sq_abs (Z.G a 1), sq_nonneg (|Z.G a 0| - |Z.G a 1|)]
    nlinarith [pow_pos hgpos 2]
  have e : σ * (Z.G a 0 * (Z.corner s 1 + t * (2 * Z.G a 1) - ρ * σ * Z.G a 0 - Z.corner s 1) -
        Z.G a 1 * (Z.corner s 0 + t * (2 * Z.G a 0) + ρ * σ * Z.G a 1 - Z.corner s 0))
      = -(ρ * (Z.G a 0 ^ 2 + Z.G a 1 ^ 2)) * (σ * σ) := by ring
  rw [e, hσ2] at hsup
  nlinarith [mul_pos hρpos hsq]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
