import CORALean.Specification.Operations.DiffPoint

/-!
# The witness difference lies in `O - U`

`diffPoint_mem_sub`: both witness points [1, Alg. 3 (exits), l. 10] reads lie in their own sets, so
the difference lies in `O - U`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both witness points lie in their own sets, so the difference lies in `O - U`. -/
theorem diffPoint_mem_sub (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (d : α →ₗ[ℝ] ℝ) :
    diffPoint wO wU d ∈ O - U :=
  Set.sub_mem_sub (wO d).mem.choose_spec.1 (wU (-d)).mem.choose_spec.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
