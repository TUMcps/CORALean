module

public import CORALean.ContSet.VPolytope.Real.Operations.DistPoint
public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# `aux_distPolyPoint` is the Euclidean distance to the polytope

For a nonempty compact set `S`, the quadratic program `min y'y - 2x'y` over `y ∈ S` minimizes
`‖x - y‖₂² - ‖x‖₂²`, so `sqrt(val + x'x)` is the Euclidean distance of `x` to `S`: exact. The
distance is `Metric.infDist` in `EuclideanSpace`, not the supremum-norm one `Vec` carries.

## Inputs
* `S` – set
* `x` – point

## Hypotheses
* `hc` – `S` compact
* `hne` – `S` nonempty

## Conclusion
* `distPoint` is the Euclidean distance from `x` to `S`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The squared Euclidean distance as the objective of the quadratic program, plus `x'x`. -/
theorem aux_dist_sq (x y : Vec ℝ n) :
    dist (toEuclidean x) (toEuclidean y) ^ 2 =
      ∑ i, y i * y i - 2 * ∑ i, x i * y i + ∑ i, x i * x i := by
  rw [dist_eq_norm, ← map_sub, norm_toEuclidean, norm₂,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.distPoint_eq {S : Set (Vec ℝ n)} (hc : IsCompact S) (hne : S.Nonempty)
    (x : Vec ℝ n) :
    VPolytope.distPoint S x =
      Metric.infDist (toEuclidean x) (toEuclidean '' S) := by -- --- PROOF ---
  -- a nearest point `y₀` of the compact set
  obtain ⟨y₀', hy₀', he⟩ :=
    (hc.image toEuclidean.continuous).exists_infDist_eq_dist (hne.image _) (toEuclidean x)
  obtain ⟨y₀, hy₀, rfl⟩ := hy₀'
  have hle : ∀ y ∈ S,
      dist (toEuclidean x) (toEuclidean y₀) ≤ dist (toEuclidean x) (toEuclidean y) :=
    fun y hy => he ▸ Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem _ hy)
  -- it minimizes the objective of the quadratic program, so the program's value is its objective
  have hleast : IsLeast ((fun y : Vec ℝ n => ∑ i, y i * y i - 2 * ∑ i, x i * y i) '' S)
      (∑ i, y₀ i * y₀ i - 2 * ∑ i, x i * y₀ i) := by
    refine ⟨⟨y₀, hy₀, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := pow_le_pow_left₀ dist_nonneg (hle y hy) 2
    rw [aux_dist_sq, aux_dist_sq] at h1
    linarith
  -- and `val + x'x` is the squared distance to `y₀`
  unfold VPolytope.distPoint
  simp only
  rw [hleast.csInf_eq, he]
  rw [show ∑ i, y₀ i * y₀ i - 2 * ∑ i, x i * y₀ i + ∑ i, x i * x i =
    dist (toEuclidean x) (toEuclidean y₀) ^ 2 from (aux_dist_sq x y₀).symm]
  exact Real.sqrt_sq dist_nonneg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
