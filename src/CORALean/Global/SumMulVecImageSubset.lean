import CORALean.Global.Tensor
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# A sum of maps, applied to one set

`[1, Lemma 2]`: `(∑ᵢ Aᵢ) S ⊆ ⨁ᵢ Aᵢ S`, the Minkowski sum on the right taking an independent
point of `S` per summand where the left takes one point for all. Equality fails as soon as
`S` has two points and two summands. Any set, any matrices.

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

namespace CORALean

open Matrix Pointwise

variable {n m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sum_mulVec_image_subset (A : Fin N → Mat ℝ n m) (S : Set (Vec ℝ m)) :
    (fun s => (∑ i, A i) *ᵥ s) '' S ⊆ ∑ i, (fun s => A i *ᵥ s) '' S := by
  rintro _ ⟨s, hs, rfl⟩
  -- the same point `s` in every summand
  rw [Set.mem_finsetSum]
  exact ⟨fun i => A i *ᵥ s, fun _ => ⟨s, hs, rfl⟩, (Matrix.sum_mulVec _ _ _).symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
