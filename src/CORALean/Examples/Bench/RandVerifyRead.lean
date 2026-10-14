import CORALean.ContSet.Zonotope.Float.Operations.Materialise
import CORALean.ContSet.Zonotope.Float.Theorems.Basic
import CORALean.Examples.Bench.RandVerifyInstance
import CORALean.Examples.Bench.RandVerifyRatExact
import CORALean.Examples.Bench.RandVerifySystem
import CORALean.Global.Float.ToRat

/-!
# `randverify`: reading the system into a number type, exactly

Every entry of `A`, `B`, `C`, every bound of `U`, and `dt` go through `inst`, the format's checked
reader: a value the format does not hold is an error naming it, never a rounding. `X0` is read as
its centre and radius, exactly where the format holds both; where it does not (the midpoint of two
`p`-bit bounds can need `p + 1` bits), the centre is rounded and the radius rounded up to cover the
whole interval, checked over ℚ: a larger initial set, which is sound, flagged `x0Enclosed`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q` in the format, exactly, `field` naming it in the error. -/
def aux_exact (inst : String → ExactDyadic → Except String 𝕋) (field : String) (q : ℚ) :
    Except String 𝕋 := do inst field (← ratExact q)

/-- A `rows × cols` matrix, entry by entry, in the format. -/
def aux_gridMatrix (inst : String → ExactDyadic → Except String 𝕋) (name : String)
    (rows cols : ℕ) (M : Array (Array ℚ)) : Except String (Array (Array 𝕋)) := do
  if M.size ≠ rows then throw s!"`{name}` has {M.size} rows, expected {rows}"
  let mut out := #[]
  for i in [0:rows] do
    let row := M.getD i #[]
    if row.size ≠ cols then throw s!"`{name}` row {i} has {row.size} entries, expected {cols}"
    out := out.push (← (List.range cols).toArray.mapM fun j =>
      aux_exact inst s!"{name}[{i}][{j}]" (row.getD j 0))
  pure out

/-- The centre and radius of `[l, h]` in the format: exact, or else enclosing it, with whether they
had to be rounded. -/
def aux_centreRadius (inst : String → ExactDyadic → Except String 𝕋) (exactIn : ExactDyadic → 𝕋)
    (field : String) (l h : ℚ) : Except String (𝕋 × 𝕋 × Bool) := do
  let c := (l + h) / 2
  let r := (h - l) / 2
  match aux_exact inst s!"{field} centre" c, aux_exact inst s!"{field} radius" r with
  | .ok cv, .ok rv => pure (cv, rv, false)
  | _, _ =>
    -- the centre rounded down, the radius up past both bounds' distance to it
    let cv : 𝕋 := FloatOps.addDown (exactIn (← ratExact c)) FloatOps.zero
    let cq := ToRat.toRat cv
    let need := max (h - cq) (cq - l)
    let rv : 𝕋 := FloatOps.addUp (exactIn (← ratExact need)) FloatOps.zero
    if ToRat.toRat rv < need then throw s!"`{field}`: no enclosing radius in the format"
    pure (cv, rv, true)

/-- A box of dimension `n`, as its `(centre, radius)`, or as its two bounds. -/
def aux_dimBox (name : String) (n : ℕ) (b : Array (ℚ × ℚ)) : Except String (Array (ℚ × ℚ)) :=
  if b.size = n then pure b else throw s!"`{name}` has dimension {b.size}, expected {n}"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The instance `I` at step `dt`, in the format `inst` reads, or why it does not fit. -/
def readRandSystem (inst : String → ExactDyadic → Except String 𝕋) (exactIn : ExactDyadic → 𝕋)
    (I : RandInstance) (dt : ℚ) : Except String (RandSystem 𝕋) := do
  -- the step and the three matrices, entry by entry
  let z : 𝕋 := FloatOps.zero
  let dtv ← aux_exact inst "dt" dt
  let A ← aux_gridMatrix inst "A" 5 5 I.A
  let B ← aux_gridMatrix inst "B" 5 2 I.B
  let C ← aux_gridMatrix inst "C" 2 5 I.C
  let x0 ← aux_dimBox "X0" 5 I.x0
  let u ← aux_dimBox "U" 2 I.u
  -- `X0` as centre and diagonal radius, exact in the format or enclosing
  let x0cr ← (List.range 5).toArray.mapM fun i =>
    aux_centreRadius inst exactIn s!"X0[{i}]" (x0.getD i (0, 0)).1 (x0.getD i (0, 0)).2
  let xc := x0cr.map (·.1)
  let xr := x0cr.map (·.2.1)
  let ulo ← (List.range 2).toArray.mapM fun i => aux_exact inst s!"U lb[{i}]" (u.getD i (0, 0)).1
  let uhi ← (List.range 2).toArray.mapM fun i => aux_exact inst s!"U ub[{i}]" (u.getD i (0, 0)).2
  -- the system, closed over the converted arrays
  let ent (M : Array (Array 𝕋)) (i j : ℕ) : 𝕋 := (M.getD i #[]).getD j z
  pure
    { A := Matrix.of fun i j => ent A i j
      B := Matrix.of fun i j => ent B i j
      C := Matrix.of fun i j => ent C i j
      X0 := Zonotope.materialise
        { h := 5
          c := fun i => xc.getD i z
          G := fun i j => if i.val = j.val then xr.getD i z else z
          I_error := ⟨fun _ => z, fun _ => z⟩ }
      U := ⟨fun i => ulo.getD i z, fun i => uhi.getD i z⟩
      dt := dtv
      x0Enclosed := x0cr.any (·.2.2) }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
