module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.ofEchelon`

[1, Sec. 4.3 (new reduction)]: the state of the generator reduction of Sec. 4.3. The generators of
`Z = {G, c}` are reordered as `[T V]`, `T ∈ ℝ^{n×n}` invertible, and kept as `T` and
`R = T⁻¹V`, so that `Z = {[T TR], c}`. This is that zonotope: the `n` columns of `T`, then
`T r` for every column `r` of `R`. "`Z̃` can be recovered after the update as `{[T TR], c}`."

## Inputs
* `n` – dimension
* `k` – column count
* `c` – center
* `T` – basis matrix
* `R` – echelon columns

## Output
* zonotope with generators `T` and `T R`

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.3 (new reduction)]: `{[T TR], c}`, `R` given by its `k` columns. -/
def Zonotope.ofEchelon {n k : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n) (R : Fin k → Vec ℝ n) :
    Zonotope (Vec ℝ n) :=
  ⟨n + k, c, Fin.append (fun i a => T a i) (fun l => T *ᵥ R l)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
