module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxSadraddini
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert
public import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct

@[expose] public section

/-!
# `reduceUnderApproxSadraddini` is an inner approximation

Whatever the solver proposes: a kept proposal meets `[1, Thm. 3]` against `Z` at `β = 0`
(the centre is shared), which is the containment half of `[1, Cor. 6]`; otherwise the
result is the centre, a point of `Z`.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceUnderApproxSadraddini_inner
    (opt : (Z : Zonotope (Vec ℝ n)) → Option (Σ h : ℕ, (Fin h → Vec ℝ n) × Mat ℝ Z.h h))
    (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.reduceUnderApproxSadraddini opt Z).construct ⊆ Z.construct := by -- --- PROOF ---
  -- the centre alone lies in `Z`
  have hc : (⟨0, Z.c, Fin.elim0⟩ : Zonotope (Vec ℝ n)).construct ⊆ Z.construct := by
    rintro _ ⟨β, -, rfl⟩
    simpa using Z.centre_mem_construct
  unfold Zonotope.reduceUnderApproxSadraddini
  split
  · exact hc
  · split_ifs with h
    · exact Zonotope.construct_subset_of_cert ⟨_, Z.c, _⟩ Z _ 0 h.1 (by simp)
        fun j => by simpa using h.2 j
    · exact hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
