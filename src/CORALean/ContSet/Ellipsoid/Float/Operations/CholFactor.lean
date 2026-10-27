module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# A Cholesky factor, computed and not trusted

`L` with `L Lᵀ ≈ Q - τ`, `τ` a margin of `2⁻³⁰` of each diagonal entry, by the column-wise Cholesky
decomposition in float arithmetic, a square root rounded down on the diagonal and a division
below it. Nothing about `L` is proved and nothing needs to be: it is a proposal, and `isPsd`
checks `Q - L Lᵀ` in outward rounding. The margin is what makes that check pass: `Q - L Lᵀ` is
then about `τ`, a diagonal matrix the rounding errors cannot outweigh, where without it the
residual would be rounding alone. A pivot not proved positive gives a zero column.

## Inputs
* `p` – Newton steps per root
* `Q` – shape matrix

## Output
* approximate Cholesky factor of `Q` less a margin
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Column `j` of the factor, from the columns before it. -/
@[step_of Ellipsoid.cholFactor]
def Ellipsoid.step_cholStep (p : ℕ) (Q : Mat 𝕋 n n) (j : Fin n) (L : Vector (Vector 𝕋 n) n) :
    Vector (Vector 𝕋 n) n :=
  let row : Fin n → Vec 𝕋 n := fun i k => (L[i.val]'i.isLt)[k.val]'k.isLt
  -- the earlier columns' share of entry `(i, j)`
  let done : Fin n → 𝕋 := fun i => sumDown fun k => if k < j then mulDown (row i k) (row j k)
    else zero
  -- the pivot, less the margin
  let τ : 𝕋 := half^[30] (absolute (Q j j))
  let d : 𝕋 := sqrtDown p (subDown (subDown (Q j j) τ) (done j))
  Vector.ofFn fun i => Vector.ofFn fun k =>
    if k = j then
      if i = j then d
      else if j < i ∧ ltStrict zero d = true then divDown (subDown (Q i j) (done i)) d
      else zero
    else row i k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An approximate Cholesky factor of `Q` less a margin; `p` Newton steps per square root. -/
def Ellipsoid.cholFactor (p : ℕ) (Q : Mat 𝕋 n n) : Mat 𝕋 n n :=
  let L₀ : Vector (Vector 𝕋 n) n := Vector.ofFn fun _ => Vector.ofFn fun _ => zero
  let L := (List.finRange n).foldl (fun L j => Ellipsoid.step_cholStep p Q j L) L₀
  fun i k => (L[i.val]'i.isLt)[k.val]'k.isLt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
