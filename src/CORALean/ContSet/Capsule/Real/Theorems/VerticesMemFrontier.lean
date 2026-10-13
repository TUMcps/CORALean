module

public import CORALean.ContSet.Capsule.Real.Operations.Vertices

@[expose] public section

/-!
# The points `Capsule.vertices` returns lie on the boundary

Every returned point is on the frontier of the capsule: points, not vertices (a capsule has
none). A point `x = c + t₀ g + r u` on a half circle, `u` a unit direction with
`(t₀ - t) (g · u) ≥ 0` for every `t ∈ [-1, 1]` (the half circle faces away from the segment), is at
distance exactly `r`
from the segment, attained at `t₀`; and `x + δ u` is at distance at least `r + δ` from every
point of it, so it is outside, however small `δ > 0`. The first half circle has `t₀ = 1` and
`g · u = ‖g‖ cos(a - θ) ≥ 0` for `a ∈ [θ - π/2, θ + π/2]`, the second `t₀ = -1` and
`cos(a - θ) ≤ 0` for `a ∈ [θ + π/2, θ + 3π/2]`. Not claimed: that the points are
the capsule's whole boundary, or that their hull is the capsule; the hull lies inside it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point at distance exactly `r` from the segment, in a direction `u` that leaves the segment
behind, is on the frontier. -/
theorem Capsule.aux_mem_frontier (C : Capsule n) (hr : 0 ≤ C.r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (-1 : ℝ) 1) (u : Vec ℝ n) (hu : ∑ i, u i ^ 2 = 1)
    (hdir : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (t₀ - t) * ∑ i, C.g i * u i) :
    (fun i => C.c i + t₀ * C.g i + C.r * u i) ∈ frontier C.construct := by -- --- PROOF ---
  -- the point is in the capsule: distance `r` at `t₀`
  have hmem : (fun i => C.c i + t₀ * C.g i + C.r * u i) ∈ C.construct := by
    refine ⟨t₀, ht₀, ?_⟩
    have : ∑ i, ((C.c i + t₀ * C.g i + C.r * u i) - (C.c i + t₀ * C.g i)) ^ 2 = C.r ^ 2 := by
      have h1 : ∀ i, ((C.c i + t₀ * C.g i + C.r * u i) - (C.c i + t₀ * C.g i)) ^ 2 =
          C.r ^ 2 * u i ^ 2 := fun i => by ring
      simp only [h1, ← Finset.mul_sum, hu, mul_one]
    rw [this, Real.sqrt_sq hr]
  refine ⟨subset_closure hmem, ?_⟩
  -- but no ball around it is inside
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set δ : ℝ := ε / 2 with hδ
  have hδpos : 0 < δ := by positivity
  -- `y = x₀ + δ u` is in the ball
  have hy : (fun i => C.c i + t₀ * C.g i + C.r * u i + δ * u i) ∈
      Metric.ball (fun i => C.c i + t₀ * C.g i + C.r * u i) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have hui : |u i| ≤ 1 := by
      have : u i ^ 2 ≤ 1 := hu ▸ Finset.single_le_sum (f := fun j => u j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
    rw [Real.dist_eq]
    have : (C.c i + t₀ * C.g i + C.r * u i + δ * u i) -
        (C.c i + t₀ * C.g i + C.r * u i) = δ * u i := by ring
    rw [this, abs_mul, abs_of_pos hδpos]
    nlinarith [abs_nonneg (u i)]
  obtain ⟨t, ht, hdist⟩ := hball hy
  -- its distance to the point `t` of the segment is more than `r`
  have hsq : ∑ i, ((C.c i + t₀ * C.g i + C.r * u i + δ * u i) - (C.c i + t * C.g i)) ^ 2 =
      (t₀ - t) ^ 2 * ∑ i, C.g i ^ 2 + 2 * (t₀ - t) * (C.r + δ) * ∑ i, C.g i * u i +
        (C.r + δ) ^ 2 := by
    have h1 : ∀ i, ((C.c i + t₀ * C.g i + C.r * u i + δ * u i) - (C.c i + t * C.g i)) ^ 2 =
        (t₀ - t) ^ 2 * C.g i ^ 2 + 2 * (t₀ - t) * (C.r + δ) * (C.g i * u i) +
          (C.r + δ) ^ 2 * u i ^ 2 := fun i => by ring
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hu, mul_one]
  have hge : (C.r + δ) ^ 2 ≤ ∑ i, ((C.c i + t₀ * C.g i + C.r * u i + δ * u i) -
      (C.c i + t * C.g i)) ^ 2 := by
    rw [hsq]
    have h2 := hdir t ht
    have h3 : 0 ≤ (t₀ - t) ^ 2 * ∑ i, C.g i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    nlinarith [mul_nonneg (by linarith : 0 ≤ C.r + δ) h2]
  have hle := (Real.sqrt_le_iff.mp hdist).2
  nlinarith
/-- The direction a half circle's point leaves in meets the generator at the angle `a - θ`. -/
theorem Capsule.aux_dot_cos (C : Capsule 2) (a : ℝ) :
    C.g 0 * Real.cos a + C.g 1 * Real.sin a =
      ‖(⟨C.g 0, C.g 1⟩ : ℂ)‖ * Real.cos (a - Complex.arg ⟨C.g 0, C.g 1⟩) := by -- --- PROOF ---
  rw [Real.cos_sub]
  have h1 := Complex.norm_mul_cos_arg (⟨C.g 0, C.g 1⟩ : ℂ)
  have h2 := Complex.norm_mul_sin_arg (⟨C.g 0, C.g 1⟩ : ℂ)
  simp only at h1 h2
  linear_combination (-Real.cos a) * h1 + (-Real.sin a) * h2

/-- The sampled angle stays within the half circle's range. -/
theorem Capsule.aux_index_range (i : Fin 500) :
    0 ≤ (i : ℝ) * (Real.pi / 499) ∧ (i : ℝ) * (Real.pi / 499) ≤ Real.pi := by -- --- PROOF ---
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have h1 : (i : ℝ) ≤ 499 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hp := Real.pi_pos
  constructor
  · positivity
  · calc (i : ℝ) * (Real.pi / 499) ≤ 499 * (Real.pi / 499) := by gcongr
      _ = Real.pi := by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vertices_mem_frontier (C : Capsule 2) (hr : 0 ≤ C.r) :
    ∀ x ∈ C.vertices, x ∈ frontier C.construct := by -- --- PROOF ---
  intro x hx
  unfold Capsule.vertices at hx
  split_ifs at hx with hp
  · -- a point capsule: its centre
    rw [List.mem_singleton] at hx
    subst hx
    have := C.aux_mem_frontier hr (t₀ := 0) (by simp) ![1, 0] (by simp [Fin.sum_univ_two])
      (by intro t _; simp [hp.1])
    convert this using 1
    funext i
    simp [hp.2]
  · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
    set θ : ℝ := Complex.arg ⟨C.g 0, C.g 1⟩ with hθ
    -- every sampled point is `c + t₀ g + r u` for a unit `u = (cos a, sin a)`
    have hunit : ∀ a : ℝ, ∑ i, (![Real.cos a, Real.sin a] : Vec ℝ 2) i ^ 2 = 1 := fun a => by
      simp [Fin.sum_univ_two]
    have hg : ∀ a : ℝ, ∑ i, C.g i * (![Real.cos a, Real.sin a] : Vec ℝ 2) i =
        C.g 0 * Real.cos a + C.g 1 * Real.sin a := fun a => by
      simp [Fin.sum_univ_two]
    have key : ∀ (t₀ a : ℝ), t₀ ∈ Set.Icc (-1 : ℝ) 1 →
        (∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (t₀ - t) * (C.g 0 * Real.cos a + C.g 1 * Real.sin a)) →
        (![C.c 0 + t₀ * C.g 0 + C.r * Real.cos a, C.c 1 + t₀ * C.g 1 + C.r * Real.sin a] :
          Vec ℝ 2) ∈ frontier C.construct := fun t₀ a ht₀ hdir => by
      have := C.aux_mem_frontier hr ht₀ ![Real.cos a, Real.sin a] (hunit a)
        (by simpa only [hg a] using hdir)
      convert this using 1
      funext i
      fin_cases i <;> simp
    -- the first half circle's points, which the closing point repeats
    have first : ∀ i : Fin 500, (![C.c 0 + 1 * C.g 0 + C.r * Real.cos (θ - Real.pi / 2 +
        (i : ℝ) * (Real.pi / 499)), C.c 1 + 1 * C.g 1 + C.r * Real.sin (θ - Real.pi / 2 +
        (i : ℝ) * (Real.pi / 499))] : Vec ℝ 2) ∈ frontier C.construct := fun i => by
      have hi := Capsule.aux_index_range i
      exact key 1 (θ - Real.pi / 2 + (i : ℝ) * (Real.pi / 499)) (by simp) (fun t ht => by
        rw [Capsule.aux_dot_cos]
        refine mul_nonneg (by linarith [ht.2]) (mul_nonneg (norm_nonneg _) ?_)
        rw [← hθ, show θ - Real.pi / 2 + (i : ℝ) * (Real.pi / 499) - θ =
          -(Real.pi / 2) + (i : ℝ) * (Real.pi / 499) by ring]
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
    · convert first i using 1
      funext j
      fin_cases j <;> simp
    · -- second half circle
      have hi := Capsule.aux_index_range i
      have := key (-1) (θ + Real.pi / 2 + (i : ℝ) * (Real.pi / 499)) (by simp) (fun t ht => by
        rw [Capsule.aux_dot_cos]
        refine mul_nonneg_of_nonpos_of_nonpos (by linarith [ht.1]) ?_
        refine mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) ?_
        rw [← hθ, show θ + Real.pi / 2 + (i : ℝ) * (Real.pi / 499) - θ =
          Real.pi / 2 + (i : ℝ) * (Real.pi / 499) by ring]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hi.1])
          (by linarith [hi.2]))
      convert this using 1
      funext j
      fin_cases j <;> simp [sub_eq_add_neg]
    · convert first 0 using 1
      funext j
      fin_cases j <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
