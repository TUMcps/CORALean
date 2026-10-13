import CORALean.ContSet.Zonotope.Real.Operations.BoundIntersect2DBisect
import CORALean.ContSet.Zonotope.Real.Theorems.BisectLowIsLeast
import CORALean.ContSet.Zonotope.Real.Theorems.MemMirrorYConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.SectionConvex

/-!
# [1, Alg. 4] returns the section of the zonogon

`{γ} × [m; M] = Z ∩ L_γ`, as printed, for a zonogon that meets the line. `m` is the lowest point
of the section (`bisectLow_isLeast`), and `M` is the lowest point of the section of the mirror image
in the x-axis, negated, which is the highest of `Z`'s; the section is an interval, so it is the
segment between them. Unlike `Alg. 3` the search needs `Z ∩ L_γ ≠ ∅`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundIntersect2DBisect_spec (Z : Zonotope (Vec ℝ 2)) (γ : ℝ)
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) :
    {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} =
      Set.Icc (Z.boundIntersect2DBisect γ).1 (Z.boundIntersect2DBisect γ).2 := by -- --- PROOF ---
  -- the lowest point of the section of `Z`, and of its mirror image
  have hm := Z.bisectLow_isLeast γ hne
  have hne' : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.mirrorY.construct := by
    obtain ⟨y, hy⟩ := hne
    refine ⟨-y, (Z.mem_mirrorY_construct _).mpr ?_⟩
    simpa using hy
  have hM := Z.mirrorY.bisectLow_isLeast γ hne'
  have hmem : ∀ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.mirrorY.construct ↔
      (![γ, -y] : Vec ℝ 2) ∈ Z.construct := fun y => by
    rw [Z.mem_mirrorY_construct]
    simp
  have hmem' : ∀ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.construct ↔
      (![γ, -y] : Vec ℝ 2) ∈ Z.mirrorY.construct := fun y => by
    rw [hmem, neg_neg]
  -- the highest point of the section of `Z` is the negative of that
  have hgreat : IsGreatest {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct}
      (-Z.mirrorY.bisectLow γ) := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [Set.mem_setOf_eq, hmem']
      simpa using hM.1
    · have := hM.2 (show -y ∈ {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.mirrorY.construct} from
        (hmem' y).mp hy)
      linarith
  refine Set.Subset.antisymm (fun y hy => ⟨hm.2 hy, hgreat.2 hy⟩) ?_
  exact (Z.section_convex γ).ordConnected.out hm.1 hgreat.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
