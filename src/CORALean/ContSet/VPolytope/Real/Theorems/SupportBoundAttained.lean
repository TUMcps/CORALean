module

public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem

@[expose] public section

/-!
# The support bound is the support function

`SupportBound` claims only that nothing exceeds the value, which leaves open how much was given
away. Over a vertex list nothing is: the supremum runs over a finite family, so some vertex takes
it, and `vertex_mem` puts that vertex in the polytope. That makes [1, Def. 3]'s `max_i ℓᵀvᵢ` an
equality rather than a bound; the maximizing vertex is the support vector of [2, Eq. 34]. A
non-empty vertex list is a hypothesis: `k = 0` denotes `∅`, which attains nothing, and a supremum
over an empty family at `ℝ` is `0` rather than `-∞`.

## Inputs
* `P` – polytope
* `c` – linear functional

## Hypotheses
* `hk` – `P` has a vertex

## Conclusion
* some point of `P` attains the support bound

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../../../references/2023/wetzlinger-hscc-support-functions.md)
* [2] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.supportBound_attained (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) (hk : 0 < P.k) :
    ∃ x ∈ P.construct, c x = (P.supportBound c).val := by
  have : Nonempty (Fin P.k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨l, hl⟩ := exists_eq_ciSup_of_finite (f := fun l : Fin P.k => c (P.V l))
  exact ⟨P.V l, P.vertex_mem l, hl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
