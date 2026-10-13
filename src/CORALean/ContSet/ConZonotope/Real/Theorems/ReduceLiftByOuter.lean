import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLiftBy
import CORALean.ContSet.ConZonotope.Real.Theorems.MemLiftEqOfMem
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepByOuter
import CORALean.ContSet.HPolytope.Real.Operations.MemEqsIff
import CORALean.ContSet.HPolytope.Real.Operations.Intersection

/-!
# Lifting, reducing and reading the rows back over-approximates

[1, Sec. 4.3]: a point of `cZ` lifts to `[x; 0]` in the lifted set (`mem_liftEq_of_mem`),
the reduction contains it (`reduceKeepBy_outer`, whichever partition), and its coefficients
`ξ` satisfy the kept inequality rows and, read at the lower coordinates, `Anew ξ = bₑ`,
which are the rows the result carries. The upper coordinates are the point itself.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLiftBy_outer (cZ : ConZonotope (Vec ℝ n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) :
    cZ.construct ⊆ (cZ.reduceLiftBy part).construct := by -- --- PROOF ---
  intro x hx
  have hlift := ConZonotope.mem_liftEq_of_mem cZ hx
  obtain ⟨ξ, hξ, hPξ, hxi⟩ := ConZonotope.mem_construct_iff.mp
    (ConZonotope.reduceKeepBy_outer cZ.liftEq part hlift)
  refine ConZonotope.mem_construct_iff.mpr ⟨ξ, hξ,
    HPolytope.mem_intersection_iff.mpr ⟨hPξ, HPolytope.mem_eqs_iff.mpr fun i => ?_⟩,
    fun k => ?_⟩
  · -- the lower coordinate of the lifted point is `0 = -bₑ i + Σ ξⱼ (G' j)(n + i)`
    have h := hxi (Fin.natAdd n i)
    have hc : (cZ.liftEq.reduceKeepBy part).c (Fin.natAdd n i) = -cZ.P.be i := by
      simp [ConZonotope.reduceKeepBy, ConZonotope.liftEq]
    rw [hc, Fin.append_right] at h
    simp only [Matrix.mulVec, dotProduct]
    have h' : ∑ j, (cZ.liftEq.reduceKeepBy part).G j (Fin.natAdd n i) * ξ j = cZ.P.be i := by
      simp only [Pi.zero_apply] at h
      linarith
    exact h'
  · have h := hxi (Fin.castAdd cZ.P.me k)
    have hc : (cZ.liftEq.reduceKeepBy part).c (Fin.castAdd cZ.P.me k) = cZ.c k := by
      simp [ConZonotope.reduceKeepBy, ConZonotope.liftEq]
    rw [hc, Fin.append_left] at h
    exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
