import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Matrix.Mul

/-!
# A bounded nonempty H-polytope has no recession direction

`{H y ≤ 0} = {0}` when `{H y ≤ h}` is bounded and nonempty: from any point `p`, every
`p + t d` with `H d ≤ 0` and `t ≥ 0` stays inside. This is what makes `{H y ≤ 0 · h}` the
set `0 · P`, the reading a convex-hull encoding gives a zero weight; for an empty `P` it
fails, `{H y ≤ 0}` being any cone the rows leave open.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.eq_zero_of_mulVec_nonpos {H : Mat ℝ q n} {h : Vec ℝ q}
    (hne : (HPolytope.ineqs H h).construct.Nonempty)
    (hb : Bornology.IsBounded (HPolytope.ineqs H h).construct) {d : Vec ℝ n}
    (hd : H *ᵥ d ≤ 0) : d = 0 := by -- --- PROOF ---
  obtain ⟨p, hp⟩ := hne
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  -- the whole ray `p + t d` lies in the polytope
  have hray : ∀ t : ℝ, 0 ≤ t → p + t • d ∈ (HPolytope.ineqs H h).construct := by
    intro t ht
    rw [HPolytope.mem_ineqs_iff] at hp ⊢
    intro i
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hp i, hd i, (Pi.zero_apply (M := fun _ => ℝ) i)]
  by_contra hd0
  have hnd : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hR0 : 0 ≤ R := (norm_nonneg p).trans (hR p hp)
  -- at `t = (2R + 1)/‖d‖` the ray leaves the ball of radius `R`
  have ht : 0 ≤ (2 * R + 1) / ‖d‖ := by positivity
  have h1 := hR _ (hray _ ht)
  have h2 : ‖((2 * R + 1) / ‖d‖) • d‖ ≤ ‖p + ((2 * R + 1) / ‖d‖) • d‖ + ‖p‖ := by
    calc ‖((2 * R + 1) / ‖d‖) • d‖ = ‖(p + ((2 * R + 1) / ‖d‖) • d) - p‖ := by
          rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, div_mul_cancel₀ _ hnd.ne'] at h2
  linarith [hR p hp]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
