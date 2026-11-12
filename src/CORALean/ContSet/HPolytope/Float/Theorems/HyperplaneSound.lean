module

public import CORALean.ContSet.HPolytope.Float.Operations.Hyperplane
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree
public import CORALean.ContSet.HPolytope.Float.Theorems.MemToSet

@[expose] public section

/-!
# A bare hyperplane denotes the points on it

If `HPolytope.hyperplane?` returns `(a, d)`, every point of the description satisfies `a·x = d`.
Error-free means the description denotes its stored rows exactly (`HPolytope.mem_toSet_iff`).

## Inputs
* `P` – halfspace description
* `x` – point

## Hypotheses
* `hx` – `x` lies in `P`

## Conclusion
* if `P` is the hyperplane `a·x = d`, then `a·x = d`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.dotProduct_of_hyperplane (P : HPolytope 𝕋 (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ P.toSet) : -- --- CONCL ---
    ∀ ad ∈ P.hyperplane?, x ⬝ᵥ toRealVec ad.1 = toReal ad.2 := by -- --- PROOF ---
  intro ad h
  unfold HPolytope.hyperplane? at h
  split_ifs at h with hP
  · cases Option.mem_some_iff.mp h
    have hmem := (HPolytope.mem_toSet_iff (HPolytope.errFree_of_isErrFree hP.1)).mp hx
    have := hmem.2 ⟨0, by omega⟩
    rw [Matrix.mulVec, dotProduct_comm] at this
    exact this
  · exact absurd h (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
