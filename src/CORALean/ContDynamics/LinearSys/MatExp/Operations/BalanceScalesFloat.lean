module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.balanceScalesFloat`, powers of two that balance `|A|`

Scales `s` for `scaledRemainderFloat`: Osborne's balancing of the matrix `N = S⁻¹|A|S`,
`N_jk = |a_jk| s_k / s_j`, with powers of two only. Index by index, the off-diagonal row sum
`Σ_{k≠i} |a_ik| s_k / s_i` and column sum `s_i Σ_{j≠i} |a_ji| / s_j` are brought within a factor
of four of each other by doubling or halving `s_i`, which divides the row by two and multiplies
the column by two; five sweeps over the indices. A row or column without off-diagonal entries
leaves its scale. Only `scaledRemainderFloat`'s bound depends on the result, and it holds for any
positive scales: this is tuning, and every value of it is sound once positive.

## Inputs
* `A` – float matrix

## Output
* float scales, powers of two
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The power of two that brings `row / f` and `col · f` within a factor of four, `fuel` doublings
or halvings at most: each doubling of `f` halves `row` and doubles `col`. -/
@[step_of MatExp.balanceScalesFloat]
def MatExp.step_balanceFactorFloat : ℕ → 𝕋 → 𝕋 → 𝕋 → 𝕋
  | 0, _, _, f => f
  | fuel + 1, row, col, f =>
    let four : 𝕋 := addUp (addUp one one) (addUp one one)
    if le (mulUp four col) row then                                          -- row ≥ 4 col
      MatExp.step_balanceFactorFloat fuel (half row) (addUp col col) (addUp f f)
    else if le (mulUp four row) col then                                     -- col ≥ 4 row
      MatExp.step_balanceFactorFloat fuel (addUp row row) (half col) (half f)
    else f

/-- One visit of index `i`: its off-diagonal row and column sums, and the scale times the
balancing factor. -/
@[step_of MatExp.balanceScalesFloat]
def MatExp.step_balanceIndexFloat (A : Mat 𝕋 n n) (s : Vector 𝕋 n) (i : Fin n) : Vector 𝕋 n :=
  let r := sumUp fun k : Fin n => if k = i then zero else mulUp (absolute (A i k)) s[k]
  let c := sumUp fun j : Fin n => if j = i then zero else divUp (absolute (A j i)) s[j]
  let row := divUp r s[i]                                                    -- Σ_{k≠i} N_ik
  let col := mulUp c s[i]                                                    -- Σ_{j≠i} N_ji
  if le row zero || le col zero then s                                       -- nothing to balance
  else s.set i (mulUp s[i] (MatExp.step_balanceFactorFloat 64 row col one))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Five sweeps of Osborne's balancing over the indices in order, from unit scales. -/
def MatExp.balanceScalesFloat (A : Mat 𝕋 n n) : Vec 𝕋 n :=
  let sweep := fun s : Vector 𝕋 n =>                                         -- i = 0, …, n-1
    (List.finRange n).foldl (fun s i => MatExp.step_balanceIndexFloat A s i) s
  let s := sweep^[5] (Vector.replicate n one)
  fun k => s[k]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
