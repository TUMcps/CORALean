module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Inclusions up to a scaled ball, read as a Hausdorff distance

`[1, Prop. 5, Eq. 40]` is how `[1, Prop. 5]` reads `d_H(X₁, X₂) ≤ D`: each set lies in the other
plus `D P_Ball`. At the supremum norm — `P_Ball` the unit box, the norm of every example in
`[1]` — that is Mathlib's `hausdorffDist` on `Vec ℝ n`. `D P_Ball` is
`{H_B x ≤ D h_B}`, the closed ball of radius `D`, by scaling at `D > 0` and because the
ball's rows admit no recession direction at `D = 0`.

## Inputs
* `S` – set of points
* `T` – set of points
* `HB` – `qB × n` matrix
* `hB` – vector of length `qB`
* `D` – real number

## Hypotheses
* `hD` – `0 ≤ D`
* `hPB` – the polytope `HB` is the unit ball
* `h₁` – `S` lies in `T + ineqs HB (D • hB)`
* `h₂` – `T` lies in `S + ineqs HB (D • hB)`

## Conclusion
* the Hausdorff distance of `S` and `T` is at most `D`

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC), 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n qB : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.hausdorffDist_le_of_subset_add_ball {S T : Set (Vec ℝ n)} {HB : Mat ℝ qB n}
    {hB : Vec ℝ qB} {D : ℝ} (hD : 0 ≤ D)
    (hPB : ∀ x, x ∈ (HPolytope.ineqs HB hB).construct ↔ ‖x‖ ≤ 1)
    (h₁ : S ⊆ T + (HPolytope.ineqs HB (D • hB)).construct)
    (h₂ : T ⊆ S + (HPolytope.ineqs HB (D • hB)).construct) : -- --- CONCL ---
    Metric.hausdorffDist S T ≤ D := by -- --- PROOF ---
  have hB0 : ∀ i, 0 ≤ hB i := fun i => by
    have := HPolytope.mem_ineqs_iff.mp ((hPB 0).mpr (by simp)) i
    simpa using this
  -- `{H_B x ≤ D h_B}` lies in the closed ball of radius `D`
  have hball : ∀ x ∈ (HPolytope.ineqs HB (D • hB)).construct, ‖x‖ ≤ D := by
    intro x hx
    have hx' := HPolytope.mem_ineqs_iff.mp hx
    rcases hD.lt_or_eq with hpos | hzero
    · have : D⁻¹ • x ∈ (HPolytope.ineqs HB hB).construct := by
        refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hpos]
        simpa using hx' i
      have h := (hPB _).mp this
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_le_iff₀ hpos,
        mul_one] at h
      exact h
    -- at `D = 0` every multiple of `x` is in the unit ball, so `x = 0`
    · subst hzero
      have hmul : ∀ t : ℝ, 0 < t → ‖t • x‖ ≤ 1 := by
        intro t ht
        refine (hPB _).mp (HPolytope.mem_ineqs_iff.mpr fun i => ?_)
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have := hx' i
        simp only [zero_smul, Pi.zero_apply] at this
        nlinarith [hB0 i]
      by_contra hne
      push Not at hne
      have h := hmul (2 / ‖x‖) (by positivity)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hne.ne'] at h
      norm_num at h
  refine Metric.hausdorffDist_le_of_mem_dist hD (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp (h₁ hx)
    exact ⟨y, hy, by rw [dist_eq_norm, add_sub_cancel_left]; exact hball z hz⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp (h₂ hx)
    exact ⟨y, hy, by rw [dist_eq_norm, add_sub_cancel_left]; exact hball z hz⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
