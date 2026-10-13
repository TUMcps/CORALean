import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul

/-!
# The accumulation of `Zonotope.cubMap`

CORA's `aux_cubMapSingle` writes the point of a zonotope as a cubic polynomial in the extended
factors `(1, β₁, ..., β_h)` and keeps one coefficient per sorted triple `k ≤ j ≤ c`, the unsorted
ones added into it. Following the steps, for output `i` and `N = h + 1`:

* `quadMat = [c,G]ᵀ T{i,k} [c,G]`, folded onto its upper triangle (`symMat`);
* `listQuad{j} = Σₖ symMat · [c,G](k, j)`, one `N × N` matrix per extended column `j`;
* the accumulation over identical factors: the entries of `listQuad{k}` whose row `j` lies below
  `k` are added into `listQuad{j}`. The loop writes only into rows `≥ j` of `listQuad{j}` and
  reads only rows `< k` of `listQuad{k}`, so every read sees the matrix as `listQuad` has it and
  the in-place loop is the closed form below.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficient of the triple `(x, y, z)` of extended columns in output `i`, the unsorted
triples folded into the sorted one: CORA's `listQuad{x}(y, z)` after the accumulation. -/
noncomputable def Zonotope.cubFold (T : Fin m → Fin n → Mat ℝ n n) (Z : Zonotope (Vec ℝ n))
    (i : Fin m) (x y z : Fin (Z.h + 1)) : ℝ :=
  -- `[c, G]`
  let Zext : Fin (Z.h + 1) → Vec ℝ n := Fin.cons Z.c Z.G
  -- `quadMat = [c,G]' * T{i,k} * [c,G]`
  let quadMat : Fin n → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ :=
    fun k a b => Zext a ⬝ᵥ (T i k *ᵥ Zext b)
  -- `quadMat - tril(quadMat,-1) + tril(quadMat,-1)'`
  let symMat : Fin n → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ := fun k a b =>
    if a < b then quadMat k a b + quadMat k b a else if a = b then quadMat k a a else 0
  -- `listQuad{j}`
  let listQuad : Fin (Z.h + 1) → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ :=
    fun j a b => ∑ k, symMat k a b * Zext j k
  -- the accumulation of identical factors
  listQuad x y z + (if x < z then listQuad z x y else 0)
    + (if x < y ∧ y < z then listQuad y x z else 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
