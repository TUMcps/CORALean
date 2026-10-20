module

public import CORALean.Specification.Specification
public import CORALean.Specification.Theorems.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# The origin in the hull of differences forces an intersection

The falsification exit of a Gilbert-Johnson-Keerthi-style check: [1, Alg. 3 (exits), l. 12]
accumulates `vᵢ = xᵢ - yᵢ` with `xᵢ` in the reachable and `yᵢ` in the unsafe set and reports
"unsafe" once their convex hull contains the origin. Sound because `O - U` is convex when `O`
and `U` are, so `convexHull_min` puts the hull inside it, and the origin there is `x = y`.
Stated over the whole accumulated set `V ⊆ O - U` rather than an indexed family.

## Inputs
* none

## Hypotheses
* `hO` – the reachable set is convex
* `hU` – the unsafe set is convex
* `hV` – the points lie in the difference set
* `h0` – the origin lies in the hull of the points

## Conclusion
* the unsafe set specification fails for the reachable set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U V : Set α}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The hull of `V` stays inside `O - U`, `O - U` being convex. -/
theorem aux_zero_mem_sub_of_convex (hO : Convex ℝ O) (hU : Convex ℝ U) (hV : V ⊆ O - U)
    (h0 : (0 : α) ∈ convexHull ℝ V) : (0 : α) ∈ O - U :=
  convexHull_min hV (hO.sub hU) h0


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.not_holds_unsafeSet_of_zero_mem_convexHull
    (hO : Convex ℝ O) (hU : Convex ℝ U) (hV : V ⊆ O - U) (h0 : (0 : α) ∈ convexHull ℝ V) :
    ¬ (Specification.unsafeSet U).Holds O := by -- --- PROOF ---
  rw [Specification.holds_unsafeSet]
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_sub.mp (aux_zero_mem_sub_of_convex hO hU hV h0)
  rw [sub_eq_zero] at hxy
  exact Set.disjoint_left.mp h hx (hxy ▸ hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
