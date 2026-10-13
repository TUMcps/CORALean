import CORALean.Specification.Specification
import CORALean.Global.LinProg.LinProg

/-!
# [1, Alg. 3 (exits), l. 10]: the witness difference along a direction

`diffPoint`: the difference between a reachable-set witness point and an unsafe-set witness
point along `d`, fed into `P̲`.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (exits), l. 10]: the difference between a reachable-set witness point
and an unsafe-set witness point along `d`, fed into `P̲`. -/
noncomputable def diffPoint (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (d : α →ₗ[ℝ] ℝ) : α :=
  (wO d).mem.choose - (wU (-d)).mem.choose

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
