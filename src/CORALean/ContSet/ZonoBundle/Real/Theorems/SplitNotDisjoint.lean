import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitInter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The halves of a split bundle need not be disjoint

A counterexample to the `Z_∩¹ ∩ Z_∩² = ∅` printed in [1, Eq. 2]: the bundle `{[-1, 1]}` in one
dimension, `Λ = 1`, split along its only column. Both halves contain `0`, the cut. The enclosure
hypothesis of `split_union` holds, so this is a split the exactness theorem covers.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Printed disjointness is false: some enclosed split has halves that meet. -/
theorem ZonoBundle.split_not_disjoint : ∃ (B : Interval (Vec ℝ 1)) (zB : ZonoBundle (Vec ℝ 1)),
    (fun x => (1 : Mat ℝ 1 1)⁻¹ *ᵥ x) '' zB.construct ⊆ B.construct ∧
      ((zB.split 1 B 0).1.construct ∩ (zB.split 1 B 0).2.construct).Nonempty := by -- --- PROOF ---
  -- the box `[-1, 1]` and the bundle holding one zonotope, the same segment
  refine ⟨⟨fun _ => -1, fun _ => 1⟩, ⟨1, fun _ => ⟨1, fun _ => 0, fun _ _ => 1⟩⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := Set.mem_iInter.1 hx (0 : Fin 1)
    intro i
    have := abs_le.mp (hβ 0)
    have h1 : (1 : Mat ℝ 1 1)⁻¹ = 1 := by simp
    simp only [h1, Matrix.one_mulVec, Entrywise.entry, Fin.sum_univ_one, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · -- `0` is the centre of both the bundle and the parallelotope, so it is in the shared cut
    rw [ZonoBundle.split_inter]
    refine ⟨(fun _ => 0 : Vec ℝ 1), ?_, ?_⟩
    · exact Set.mem_iInter.2 fun i => ⟨fun _ => 0, fun _ => by simp, by simp⟩
    · refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
      funext i
      simp [ZonoBundle.parallelotope, Zonotope.mtimes, Interval.zonotope]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
