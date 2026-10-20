module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Real.Theorems.MatNormIsGreatest

@[expose] public section

/-!
# `norm` of a matrix zonotope bounds the norm of its members

CORA's `@matZonotope/norm` is the norm of `intervalMatrix(matZ)`, the box `C ± Σ |Gᵢ|` around the
zonotope: the largest norm over the box, which `matNorm_isGreatest` attains. The box contains the
zonotope (`interval_contains`), so the number bounds the norm of every member from above. CORA's
help text calls it an approximate maximum norm, and it is no more: a box is larger than its
zonotope.

## Inputs
* `p` – norm type
* `Z` – matrix zonotope
* `M` – matrix

## Hypotheses
* `hM` – `M` lies in `Z`

## Conclusion
* the norm of `M` is bounded by that of the interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- No member of the matrix zonotope has a larger norm than `norm(intervalMatrix(matZ), type)`. -/
theorem Zonotope.matNorm_le (p : Interval.NormType) (Z : Zonotope (Mat ℝ m n)) {M : Mat ℝ m n}
    (hM : M ∈ Z.construct) : p.eval M ≤ Interval.matNorm p Z.interval := by
  have hI := Z.interval_contains hM
  have hne : ∀ r s, Z.interval.inf r s ≤ Z.interval.sup r s := fun r s =>
    (Interval.mem_mat_iff.mp hI r s).1.trans (Interval.mem_mat_iff.mp hI r s).2
  exact (Interval.matNorm_isGreatest p Z.interval hne).2 ⟨M, hI, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
