import CORALean.Global.CubeSubsetHalfspaceIff
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Jensen

/-!
# Circumradius and polar inradius are reciprocal

`[1, Lemma 4]`: for a polytope `P = conv(v₁, …, v_N)` with a nonzero vertex,
`R₁(P) = 1 / r∞(P^Δ)`, the `1`-norm circumradius against the `∞`-norm inradius of the
polar `P^Δ = {x | yᵀx ≤ 1 for all y ∈ P}`. Both are `max ‖vᵢ‖₁`: the convex `1`-norm peaks
at a vertex, and a cube lies in `P^Δ` iff it lies in each halfspace `{vᵢᵀ x ≤ 1}`
(`[1, Lemma 4, Eq. 26]`), which is `[1, Lemma 3]` vertex by vertex. Neither symmetry nor full
dimension is used.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem l1Circumradius_eq_inv_inradius_polar (v : Fin N → Vec ℝ n) (hv : ∃ i, v i ≠ 0) :
    ∃ R r, IsGreatest ((fun x => ∑ j, |x j|) '' convexHull ℝ (Set.range v)) R ∧
      IsGreatest {r | 0 ≤ r ∧ ∀ x : Vec ℝ n, ‖x‖ ≤ r →
        ∀ y ∈ convexHull ℝ (Set.range v), ∑ j, y j * x j ≤ 1} r ∧
        R = 1 / r := by -- --- PROOF ---
  obtain ⟨i₀, hi₀⟩ := hv
  have hN : (Finset.univ : Finset (Fin N)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  set M : ℝ := Finset.univ.sup' hN fun i => ∑ j, |v i j| with hM
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' hN fun i => ∑ j, |v i j|
  have hMeq : M = ∑ j, |v i₁ j| := hi₁
  have hle : ∀ i, ∑ j, |v i j| ≤ M := fun i => Finset.le_sup' (fun i => ∑ j, |v i j|)
    (Finset.mem_univ i)
  have hMpos : 0 < M := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hi₀
    exact lt_of_lt_of_le (lt_of_lt_of_le (abs_pos.mpr hj) (Finset.single_le_sum
      (f := fun j => |v i₀ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))) (hle i₀)
  -- the `1`-norm is convex
  have hconv : ConvexOn ℝ Set.univ fun x : Fin n → ℝ => ∑ j, |x j| := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  refine ⟨M, 1 / M, ⟨⟨v i₁, subset_convexHull ℝ _ ⟨i₁, rfl⟩, hMeq.symm⟩, ?_⟩, ?_, by simp⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, h⟩ :=
      ConvexOn.exists_ge_of_mem_convexHull hconv (Set.subset_univ _) hy
    exact h.trans (hle i)
  -- a cube lies in the polar iff `r ‖vᵢ‖₁ ≤ 1` for every vertex
  · have key : ∀ r : ℝ, 0 ≤ r → ((∀ x : Vec ℝ n, ‖x‖ ≤ r →
        ∀ y ∈ convexHull ℝ (Set.range v), ∑ j, y j * x j ≤ 1) ↔ r * M ≤ 1) := by
      intro r hr
      constructor
      · intro h
        rw [hMeq]
        exact ((cube_subset_halfspace_iff (v i₁)).1 r hr).mp fun x hx =>
          h x hx _ (subset_convexHull ℝ _ ⟨i₁, rfl⟩)
      · intro h x hx y hy
        -- the halfspace is convex and holds every vertex
        refine convexHull_min (t := {y : Vec ℝ n | ∑ j, y j * x j ≤ 1}) ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          exact ((cube_subset_halfspace_iff (v i)).1 r hr).mpr
            ((mul_le_mul_of_nonneg_left (hle i) hr).trans h) x hx
        · refine (convex_halfSpace_le ?_ 1)
          exact ⟨fun a b => by simp [add_mul, Finset.sum_add_distrib],
            fun c a => by simp [mul_assoc, Finset.mul_sum]⟩
    refine ⟨⟨by positivity, (key _ (by positivity)).mpr (by field_simp; rfl)⟩, ?_⟩
    rintro r ⟨hr, h⟩
    rw [le_div_iff₀ hMpos]
    simpa using (key r hr).mp h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
