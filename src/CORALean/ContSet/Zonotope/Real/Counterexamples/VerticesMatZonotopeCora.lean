module

public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-!
# `Zonotope.vec2matCora`: the one-argument `vec2mat` of `vertices(matZonotope)`

`@matZonotope/vertices.m` (l. 38) turns each vertex `V(:,i)`, the stacked entries of an `n × m`
matrix (`zonotope(matZ)` reshapes `C` and `G` to columns), back into a matrix with
`vec2mat(V(:,i))`, one argument. `global/functions/matlab/converter/vec2mat.m` then assumes a
square matrix, `cols = sqrt(length(vec))` (l. 36-37), and returns `reshape(vec, [], cols)`: for a
length that is a perfect square `s²` an `s × s` matrix, and for any other length a non-integer
size argument, which `reshape` rejects. So the vertices of an `n × m` matrix zonotope are `n × m`
only if `n = m`. Modelled: the length of the vector and the shape of the result. Read from the
source, not run.

# CORA's `vertices(matZonotope)` is wrong for a non-square matrix zonotope

For `matZonotope(zeros(1,4), ones(1,4))` the two vertices come back as `2 × 2` matrices; for
`matZonotope(zeros(2,3), ones(2,3))` the call stops.

## Inputs
* `n` – row count
* `m` – column count

## Hypotheses
* `hnm` – dimensions differ

## Conclusion
* the vertices come back with the wrong shape
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- `vec2mat(vec)` for a vector of length `len`: `none` is the error of `reshape` with a
non-integer size, otherwise the shape (rows, columns) of the matrix. -/
def Zonotope.vec2matCora (len : ℕ) : Option (ℕ × ℕ) :=
  if Nat.sqrt len * Nat.sqrt len = len then some (Nat.sqrt len, Nat.sqrt len) else none


-- =======================================  MAIN THEOREM  ======================================= --

/-- The vertices of an `n × m` matrix zonotope come back with the wrong shape if `n ≠ m`. -/
theorem Zonotope.vec2mat_cora_ne {n m : ℕ} (hnm : n ≠ m) : -- --- CONCL ---
    Zonotope.vec2matCora (n * m) ≠ some (n, m) := by -- --- PROOF ---
  unfold Zonotope.vec2matCora
  split_ifs with h
  · simp only [ne_eq, Option.some.injEq, Prod.mk.injEq]
    rintro ⟨h1, h2⟩
    exact hnm (h1.symm.trans h2)
  · simp

/-- `1 × 4`: a `2 × 2` matrix. -/
example : Zonotope.vec2matCora (1 * 4) = some (2, 2) := by
  have h : Nat.sqrt 4 = 2 := (Nat.eq_sqrt.2 ⟨by omega, by omega⟩).symm
  simp [Zonotope.vec2matCora, h]

/-- `2 × 3`: the error. -/
example : Zonotope.vec2matCora (2 * 3) = none := by
  have h : Nat.sqrt 6 = 2 := (Nat.eq_sqrt.2 ⟨by omega, by omega⟩).symm
  simp [Zonotope.vec2matCora, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
