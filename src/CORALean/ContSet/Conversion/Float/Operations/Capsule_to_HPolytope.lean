module

public import CORALean.ContSet.Capsule.Float.Operations.BoundDotUp
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A capsule as halfspaces, over a floating-point scalar, as CORA's `polytope(C)` dispatches

`@capsule/polytope.m` at `n = 1` is the box (`aux_1D`), here rounded outward. Otherwise the rows are
`[B'; -B']`, `B = gramSchmidt(g)`, each at the capsule's support value along it
(`aux_supportFunction`, `Capsule.boundDotUp`, every term rounded up and the error box added). The
basis is CORA's computed in floats, the length `normUp p`; the rows are sound whatever basis came
out. At `g = 0` it is the identity. CORA's point and segment branches are these rows at `g = 0` or
`r = 0`; over floats an equality is a slab anyway, so there is no branch of its own for them.

## Inputs
* `p` – Newton steps per row length

## Output
* halfspace polytope enclosing the capsule
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {k m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The column CORA's completion drops: the first largest `|gᵢ|`. -/
def Capsule.aux_pivot (g : Vec 𝕋 (m + 1)) : Fin (m + 1) :=
  (List.finRange (m + 1)).foldl
    (fun best i => if le (absolute (g i)) (absolute (g best)) then best else i) 0

/-- One pass of CORA's loop: `v = b - Σ (qᵀ b) q` over the columns so far, then `v / ‖v‖₂`. -/
def Capsule.aux_gramSchmidtStep (p : ℕ) (Q : List (Vec 𝕋 k)) (b : Vec 𝕋 k) : List (Vec 𝕋 k) :=
  let v : Vec 𝕋 k := fun i =>
    subUp (b i) (sumUp fun l : Fin Q.length => mulUp (dotUp Q[l] b) (Q[l] i))
  Q ++ [fun i => divUp (v i) (normUp p v)]

/-- CORA's `gramSchmidt(g)` in floats: `g`, the unit columns but the pivot's, orthonormalized. -/
def Capsule.aux_basis (p : ℕ) (g : Vec 𝕋 (m + 1)) : Mat 𝕋 (m + 1) (m + 1) :=
  if (List.finRange (m + 1)).all fun i => le (absolute (g i)) zero then
    diagonalBlock fun _ => one
  else
    let e : Fin m → Vec 𝕋 (m + 1) := fun l i =>
      if i = (Capsule.aux_pivot g).succAbove l then one else zero
    let cols := List.ofFn (Fin.cases (motive := fun _ => Vec 𝕋 (m + 1)) g e)
    let Q := cols.foldl (Capsule.aux_gramSchmidtStep p) []
    fun i j => (Q.getD j fun _ => zero) i

variable [SoundFloatArithmetic 𝕋]

/-- CORA's `aux_supportFunction`: the rows `[B'; -B']`, each at its support value. -/
def Capsule.aux_supportFunction (p : ℕ) (C : Capsule 𝕋 (m + 1)) :
    HPolytope 𝕋 (Vec 𝕋 (m + 1)) :=
  let B := Capsule.aux_basis p C.g
  let A : Mat 𝕋 ((m + 1) + (m + 1)) (m + 1) := Fin.append Bᵀ (-Bᵀ)
  HPolytope.ofBounds A fun i => C.boundDotUp (A i) (fun _ => rfl) p


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polytope(C, 'outer')`; `p` Newton steps for each row's length. -/
def Capsule.hPolytope (p : ℕ) : {n : ℕ} → Capsule 𝕋 n → HPolytope 𝕋 (Vec 𝕋 n)
  | 0, C => C.interval.hPolytope
  | m + 1, C =>
    -- 1. `n = 1`: `aux_1D`, the box `c ± (|g| + r)` rounded outward
    if m = 0 then C.interval.hPolytope
    -- 2. otherwise, the point and the segment included: `aux_supportFunction`
    else C.aux_supportFunction p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
