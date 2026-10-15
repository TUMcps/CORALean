module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.Global.EuclideanNorm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# An ellipsoid that is no polytope

A polytope is a convex hull of finitely many points, and the closed unit disc is not one. Were it
`V.construct`, every unit vector `d` would be a convex combination of the vertices, so one vertex
`v` would have `d · v ≥ 1`; a vertex lies in the disc, so `|v - d|² ≤ 1 - 2 d · v + 1 ≤ 0` and `v =
d`. Every unit vector would then be a vertex, and there are infinitely many of them.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The points of the unit ellipsoid in the plane: the closed unit disc. -/
theorem Ellipsoid.aux_mem_disc (x : Vec ℝ 2) :
    x ∈ (⟨1, 0, .one⟩ : Ellipsoid 2).construct ↔ x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by -- --- PROOF ---
  have hG : (⟨1, 0, .one⟩ : Ellipsoid 2).G = 1 := CFC.sqrt_one
  have hball : x ∈ (⟨1, 0, .one⟩ : Ellipsoid 2).construct ↔ ‖x‖₂ ≤ 1 :=
    ⟨fun ⟨u, hu, hx⟩ => by rw [hx, hG, Matrix.one_mulVec, zero_add]; exact hu,
      fun h => ⟨x, h, by rw [hG, Matrix.one_mulVec, zero_add]⟩⟩
  have hsq : ‖x‖₂ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [norm₂_sq, Fin.sum_univ_two]
  rw [hball, ← hsq]
  constructor
  · intro h
    nlinarith [norm₂_nonneg x]
  · intro h
    nlinarith [norm₂_nonneg x]

/-- The unit vectors `((1 - t²)/(1 + t²), 2t/(1 + t²))`, one for each natural number `t`. -/
theorem Ellipsoid.aux_unit_family (t : ℕ) :
    ∃ d : Vec ℝ 2, d 0 ^ 2 + d 1 ^ 2 = 1 ∧
      d 0 = (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2) := by -- --- PROOF ---
  have hpos : (1 : ℝ) + (t : ℝ) ^ 2 ≠ 0 := by positivity
  refine ⟨fun i => if i = 0 then (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2)
    else 2 * t / (1 + (t : ℝ) ^ 2), ?_, by simp⟩
  simp only [Fin.isValue, if_true, one_ne_zero, if_false]
  field_simp
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.exists_not_vPolytope :
    ∃ E : Ellipsoid 2, ¬ ∃ V : VPolytope (Vec ℝ 2), V.construct = E.construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, .one⟩, ?_⟩
  rintro ⟨V, hV⟩
  -- every vertex is in the disc
  have hvert : ∀ j, V.V j 0 ^ 2 + V.V j 1 ^ 2 ≤ 1 := fun j => by
    refine (Ellipsoid.aux_mem_disc _).mp (hV ▸ ?_)
    refine ⟨fun i => if i = j then 1 else 0, fun i => by positivity, by simp, ?_⟩
    simp [Finset.sum_ite_eq']
  -- every unit vector is a vertex
  have hunit : ∀ d : Vec ℝ 2, d 0 ^ 2 + d 1 ^ 2 = 1 → ∃ j, V.V j = d := fun d hd => by
    obtain ⟨β, hβ0, hβ1, hdβ⟩ := hV ▸ (Ellipsoid.aux_mem_disc d).mpr hd.le
    -- the dot product of `d` with a vertex is at most `1`, and on average it is `1`
    have hdot : ∀ j, d 0 * V.V j 0 + d 1 * V.V j 1 ≤ 1 := fun j => by
      nlinarith [hvert j, sq_nonneg (d 0 - V.V j 0), sq_nonneg (d 1 - V.V j 1)]
    have havg : ∑ j, β j * (d 0 * V.V j 0 + d 1 * V.V j 1) = 1 := by
      have h0 := congrFun hdβ 0
      have h1 := congrFun hdβ 1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
      calc ∑ j, β j * (d 0 * V.V j 0 + d 1 * V.V j 1)
          = d 0 * ∑ j, β j * V.V j 0 + d 1 * ∑ j, β j * V.V j 1 := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 1 := by rw [← h0, ← h1]; linarith
    -- so some vertex reaches `1`
    obtain ⟨j, hj⟩ : ∃ j, 1 ≤ d 0 * V.V j 0 + d 1 * V.V j 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i, hi⟩ : ∃ i, 0 < β i := by
        by_contra h
        push Not at h
        have : ∑ j, β j ≤ 0 := Finset.sum_nonpos fun j _ => h j
        linarith
      have : ∑ j, β j * (d 0 * V.V j 0 + d 1 * V.V j 1) < ∑ j, β j :=
        Finset.sum_lt_sum (fun j _ => by nlinarith [hβ0 j, hcon j])
          ⟨i, Finset.mem_univ i, by nlinarith [hcon i]⟩
      linarith
    refine ⟨j, funext fun i => ?_⟩
    have h0 : (V.V j 0 - d 0) ^ 2 + (V.V j 1 - d 1) ^ 2 ≤ 0 := by
      nlinarith [hvert j]
    fin_cases i
    · simpa using by nlinarith [sq_nonneg (V.V j 0 - d 0), sq_nonneg (V.V j 1 - d 1)]
    · simpa using by nlinarith [sq_nonneg (V.V j 0 - d 0), sq_nonneg (V.V j 1 - d 1)]
  -- but there are infinitely many unit vectors, and only finitely many vertices
  choose u hu1 hu0 using Ellipsoid.aux_unit_family
  choose f hf using fun t => hunit (u t) (hu1 t)
  have hinj : Function.Injective f := fun s t hst => by
    have h : u s = u t := by rw [← hf s, ← hf t, hst]
    have h0 := congrFun h 0
    rw [hu0 s, hu0 t] at h0
    have hs : (0 : ℝ) < 1 + (s : ℝ) ^ 2 := by positivity
    have ht : (0 : ℝ) < 1 + (t : ℝ) ^ 2 := by positivity
    rw [div_eq_div_iff hs.ne' ht.ne'] at h0
    have : (s : ℝ) ^ 2 = (t : ℝ) ^ 2 := by nlinarith
    exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg s) (Nat.cast_nonneg t)).mp this
  exact not_injective_infinite_finite f hinj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
