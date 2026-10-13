module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# An affine map of an AH-polytope

`[1, Eq. 5]`: `G (x̄ + X P) + g = (G x̄ + g) + G X P`. AH-polytopes are closed under affine
maps with no new rows, which is half of why the encodings in `[1]` are stated for them.

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

open Matrix

variable {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.image_affine_ahPolytope (G : Mat ℝ k n) (g : Vec ℝ k) (xbar : Vec ℝ n)
    (X : Mat ℝ n m) (P : HPolytope (Vec ℝ m)) :
    (fun x => G *ᵥ x + g) '' HPolytope.ahPolytope xbar X P
      = HPolytope.ahPolytope (G *ᵥ xbar + g) (G * X) P := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by simp only [mulVec_add, mulVec_mulVec]; abel⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨xbar + X *ᵥ p, ⟨p, hp, rfl⟩, by simp only [mulVec_add, mulVec_mulVec]; abel⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
