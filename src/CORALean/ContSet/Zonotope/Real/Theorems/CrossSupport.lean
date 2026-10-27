module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A planar zonotope lies on one side of each edge line

[1, Alg. 3] and [1, Alg. 4] walk the vertices of a zonogon along its generators. At a vertex
`corner s` and a generator `a` flipped from `-` to `+` there, the segment `[corner s; corner s +
2 g_a]` is an edge when the generators before `a` (those with `s = +`) have `σ·cross(g_b, g_a) ≥ 0`
and those after it `σ·cross(g_a, g_c) ≥ 0`, and the zonogon is then on one side of its line:
`σ·cross(g_a, z - corner s) ≥ 0`. `σ = 1` is the counter-clockwise walk of increasing angle,
`σ = -1` the clockwise one; no ordering of the indices is assumed.

## Inputs
* `Z` – planar zonotope
* `σ` – orientation sign
* `s` – corner signs
* `a` – generator index
* `z` – point

## Hypotheses
* `ha` – sign of `a` is false
* `hB` – positive-sign generators lie on the correct side
* `hC` – other negative-sign generators lie on the correct side
* `hz` – `z` lies in `Z`

## Conclusion
* `z` lies on the supported side of generator `a`

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cross_support (Z : Zonotope (Vec ℝ 2)) (σ : ℝ) (s : Fin Z.h → Bool)
    (a : Fin Z.h) (ha : s a = false)
    (hB : ∀ b, s b = true → 0 ≤ σ * (Z.G b 0 * Z.G a 1 - Z.G b 1 * Z.G a 0))
    (hC : ∀ c, s c = false → c ≠ a → 0 ≤ σ * (Z.G a 0 * Z.G c 1 - Z.G a 1 * Z.G c 0))
    {z : Vec ℝ 2} (hz : z ∈ Z.construct) : -- --- CONCL ---
    0 ≤ σ * (Z.G a 0 * (z - Z.corner s) 1 - Z.G a 1 * (z - Z.corner s) 0) := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  -- the difference to the corner, coordinatewise
  have key : ∀ k : Fin 2, (Z.c + ∑ j, β j • Z.G j - Z.corner s) k
      = ∑ j, (β j - (if s j then (1 : ℝ) else -1)) * Z.G j k := by
    intro k
    simp only [Zonotope.corner, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [key 0, key 1]
  have hsum : σ * (Z.G a 0 * ∑ j, (β j - (if s j then (1 : ℝ) else -1)) * Z.G j 1
      - Z.G a 1 * ∑ j, (β j - (if s j then (1 : ℝ) else -1)) * Z.G j 0)
      = ∑ j, (β j - (if s j then (1 : ℝ) else -1)) *
        (σ * (Z.G a 0 * Z.G j 1 - Z.G a 1 * Z.G j 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  -- each term is a product of two factors of the same sign
  refine Finset.sum_nonneg fun j _ => ?_
  have hb := abs_le.mp (hβ j)
  by_cases hj : j = a
  · subst hj
    ring_nf
    exact le_rfl
  · cases hsj : s j
    · have := hC j hsj hj
      simp only [Bool.false_eq_true, if_false]
      nlinarith [hb.1]
    · have := hB j hsj
      simp only [if_true]
      have e : σ * (Z.G a 0 * Z.G j 1 - Z.G a 1 * Z.G j 0)
          = -(σ * (Z.G j 0 * Z.G a 1 - Z.G j 1 * Z.G a 0)) := by ring
      rw [e]
      nlinarith [hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
