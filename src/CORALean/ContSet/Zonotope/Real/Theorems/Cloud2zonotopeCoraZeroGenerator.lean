module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `cloud2zonotope`'s step 8 can cut a zero generator from a cloud with extent

[1, Alg. 3, step 8]: `g := ratio |u · rad| u`, with `rad` the cloud's interval radius, which the
text calls "a fraction of (an approximation of) the largest projection of the points along `u`".
But `u · rad` is signed in `u`: for the cloud `{(1, -1), (-1, 1)}` the first principal direction is
`u = (1, -1) / √2`, which carries all of the cloud (`Σⱼ (u · xⱼ)² = Σⱼ ‖xⱼ‖² = 4`), yet
`rad = (1, 1)` and `u · rad = 0`: `g = 0` whatever the ratio. Step 2 of `compress`, `u = g / ‖g‖`,
is then `0 / 0`. CORA's `aux_cloud2zonotope` (`enclosePoints(points, 'maiga')`) does exactly this
and divides `0 / 0` in MATLAB, so the points become `NaN`; Lean's `x / 0 = 0` makes
`cloud2zonotopeCompress` the identity there. Only the vanishing of `g` is stated.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cloud2zonotopeCora_zeroGenerator :
    ∃ (pts : Fin 2 → Vec ℝ 2) (u : Vec ℝ 2),
      ‖u‖₂ = 1 ∧ (∑ j, (u ⬝ᵥ pts j) ^ 2 = ∑ j, ‖pts j‖₂ ^ 2) ∧ (∃ j, u ⬝ᵥ pts j ≠ 0) ∧
      u ⬝ᵥ (Interval.enclosePoints pts).radius = 0 ∧
      ∀ ratio : ℝ,
        (ratio * |u ⬝ᵥ (Interval.enclosePoints pts).radius|) • u = 0 := by -- --- PROOF ---
  -- the cloud, and its radius `(1, 1)` coordinate by coordinate
  set pts : Fin 2 → Vec ℝ 2 := ![![1, -1], ![-1, 1]] with hpts
  have hof : ∀ (f : Fin 2 → ℝ) (i : Fin 2), (Entrywise.ofEntry f : Vec ℝ 2) i = f i :=
    fun _ _ => rfl
  have hent : ∀ (v : Fin 2 → ℝ) (i : Fin 2),
      Entrywise.entry (α := Vec ℝ 2) (ι := Fin 2) v i = v i := fun _ _ => rfl
  have hrad : (Interval.enclosePoints pts).radius = ![1, 1] := by
    funext i
    fin_cases i <;>
      simp [Interval.radius, Interval.enclosePoints, hpts, hof, hent, Fin.univ_succ] <;> norm_num
  -- the direction `u = (1, -1) / √2` and the five facts about it
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨pts, ![Real.sqrt 2 / 2, -(Real.sqrt 2 / 2)], ?_, ?_, ⟨0, ?_⟩, ?_, ?_⟩
  · simp only [norm₂, Fin.sum_univ_two]
    simp [div_pow, hs]
    norm_num
  · simp [norm₂, Fin.sum_univ_two, dotProduct, hpts]
    nlinarith [hs]
  · simp [dotProduct, hpts, Fin.sum_univ_two]
  · rw [hrad]
    simp [dotProduct, Fin.sum_univ_two]
  · intro ratio
    rw [hrad]
    simp [dotProduct, Fin.sum_univ_two]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
