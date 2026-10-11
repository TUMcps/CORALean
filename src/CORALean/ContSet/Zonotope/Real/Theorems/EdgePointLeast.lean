import CORALean.ContSet.Zonotope.Real.Theorems.CrossSupport
import CORALean.ContSet.Zonotope.Real.Theorems.CornerMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Segment

/-!
# A point of an edge on the line is the lowest point of the section

For the edge `[corner s; corner s + 2 g_a]` of the kind `cross_support` describes, with `a` pointing
along `σ` in `x` (`σ g_{a,x} > 0`), any point of the edge on a vertical line is the lowest point
of the zonogon on that line: the zonogon is on one side of the edge's line, and on a vertical line
that side is the side of larger `y`. It is the last step of [1, Alg. 4] (lines 27-28), where the
edge is `[P; P + s]` for the one generator left in `G`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.edge_point_least (Z : Zonotope (Vec ℝ 2)) (σ : ℝ) (s : Fin Z.h → Bool)
    (a : Fin Z.h) (ha : s a = false)
    (hB : ∀ b, s b = true → 0 ≤ σ * (Z.G b 0 * Z.G a 1 - Z.G b 1 * Z.G a 0))
    (hC : ∀ c, s c = false → c ≠ a → 0 ≤ σ * (Z.G a 0 * Z.G c 1 - Z.G a 1 * Z.G c 0))
    (haX : 0 < σ * Z.G a 0) {z : Vec ℝ 2}
    (hz : z ∈ segment ℝ (Z.corner s) (Z.corner s + (2 : ℝ) • Z.G a)) :
    z ∈ Z.construct ∧
      ∀ y' : ℝ, (![z 0, y'] : Vec ℝ 2) ∈ Z.construct → z 1 ≤ y' := by -- --- PROOF ---
  -- the far end of the edge is also a corner: `a` flipped to `+`
  have hend : Z.corner s + (2 : ℝ) • Z.G a ∈ Z.construct := by
    refine ⟨fun j => (if s j then (1 : ℝ) else -1) + (if j = a then 2 else 0), fun j => ?_, ?_⟩
    · show |(if s j = true then (1 : ℝ) else -1) + (if j = a then 2 else 0)| ≤ 1
      by_cases hj : j = a
      · subst hj; simp [ha]; norm_num
      · cases hsj : s j <;> simp [hj]
    · simp only [Zonotope.corner, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      module
  refine ⟨Z.convex_construct.segment_subset (Z.corner_mem_construct s) hend hz, fun y' hy' => ?_⟩
  -- the point is `P + t (2 g_a)` on the edge
  rw [segment_eq_image'] at hz
  obtain ⟨t, -, hzt⟩ := hz
  obtain rfl : z = Z.corner s + t • (Z.corner s + (2 : ℝ) • Z.G a - Z.corner s) := hzt.symm
  have hsup := Z.cross_support σ s a ha hB hC hy'
  have e0 : (![(Z.corner s + t • (Z.corner s + (2 : ℝ) • Z.G a - Z.corner s)) 0, y'] - Z.corner s
      : Vec ℝ 2) 0 = t * (2 * Z.G a 0) := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    ring
  have e1 : (![(Z.corner s + t • (Z.corner s + (2 : ℝ) • Z.G a - Z.corner s)) 0, y'] - Z.corner s
      : Vec ℝ 2) 1 = y' - Z.corner s 1 := rfl
  have e2 : (Z.corner s + t • (Z.corner s + (2 : ℝ) • Z.G a - Z.corner s)) 1
      = Z.corner s 1 + t * (2 * Z.G a 1) := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e0, e1] at hsup
  rw [e2]
  have h3 : 0 ≤ (σ * Z.G a 0) * (y' - (Z.corner s 1 + t * (2 * Z.G a 1))) := by nlinarith [hsup]
  have := nonneg_of_mul_nonneg_right h3 haX
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
