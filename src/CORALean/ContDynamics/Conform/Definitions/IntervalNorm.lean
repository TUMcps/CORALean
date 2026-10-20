module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The sizes a conformance synthesis minimizes

`intervalNorm σ G = σᵀ|G| 1`, the weighted sum of the interval hull's edge lengths of a
zonotope with generators `G`, center left out: [2, Eq. 11], [3, Def. 3] at `σ = 1`, and
[1, Def. 2]. With the center put back as a generator it is Sec. 3.1's `‖·‖_{Ĩ,σ}`.

`frobNormSq P G = trace(Gᵀ P G)`, the square of [2, Eq. 22]'s `‖·‖_{F,P}`. Both depend on the
generators, not on the set.

## Inputs
* `m` – dimension
* `ι` – generator index type
* `σ` – weights
* `G` – generators

## Output
* the weighted sum of the interval hull's edge lengths

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
* [3] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [2, Eq. 11]: `σᵀ |G| 1`. -/
noncomputable def Conform.intervalNorm {m : ℕ} {ι : Type} [Fintype ι] (σ : Vec ℝ m)
    (G : ι → Vec ℝ m) : ℝ :=
  ∑ j, ∑ a, σ a * |G j a|

/-- [2, Eq. 22], squared: `trace(Gᵀ P G)`. -/
noncomputable def Conform.frobNormSq {m : ℕ} {ι : Type} [Fintype ι] (P : Mat ℝ m m)
    (G : ι → Vec ℝ m) : ℝ :=
  ∑ j, G j ⬝ᵥ (P *ᵥ G j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
