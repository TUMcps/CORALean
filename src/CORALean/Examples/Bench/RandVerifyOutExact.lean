import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Global.Float.ToRat
import CORALean.Examples.Bench.RandVerifyOutZono

/-!
# `randverify`: `Y = C · R` exactly

The window `R` (centre `c`, generators `G`, error box `E`) mapped by `C` over ℚ, with no
rounding: the centre is `C (c + mid E)`, the generators are `C g_j` and `C e_i rad_i E`, one per
error-box dimension of nonzero radius; a zero generator is dropped. `C` is the instance's own
exact matrix. Every entry of `R` and of `C` is first put over a common denominator, so the
product is taken in integers: `2 D` for `R` (twice, for the midpoint and radius of `E`), `D_C`
for `C`, and `2 D D_C` for `Y`. The result is the set `C · R` denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q · den` as an integer, `den` a multiple of `q.den`. -/
def aux_scaleTo (den : ℕ) (q : ℚ) : ℤ := q.num * ((den / q.den : ℕ) : ℤ)

/-- The least common denominator of `qs`. -/
def aux_lcmDen (qs : Array ℚ) : ℕ := qs.foldl (fun d q => Nat.lcm d q.den) 1

/-- `C v` in integers, row by row, `C` as `5` entries per row. -/
def aux_apply (C : Array ℤ) (v : Array ℤ) : ℤ × ℤ :=
  let row (i : ℕ) : ℤ := (List.range 5).foldl (fun s k => s + C.getD (5 * i + k) 0 * v.getD k 0) 0
  (row 0, row 1)


-- =====================================  MAIN DEFINITION  ====================================== --

def outputZonoExact (C : Array (Array ℚ)) (R : Zonotope (Vec 𝕋 5)) : RandOutZono :=
  -- `C` over `D_C`, row-major
  let cq : Array ℚ := (C.getD 0 #[]).extract 0 5 ++ (C.getD 1 #[]).extract 0 5
  let dC := aux_lcmDen cq
  let ci := cq.map (aux_scaleTo dC)
  -- every entry of `R` exactly, then over one denominator `D`
  let fin5 := (List.finRange 5).toArray
  let idx := (List.range 5).toArray
  let c := fin5.map fun k => ToRat.toRat (R.c k)
  let lo := fin5.map fun k => ToRat.toRat (R.E.inf k)
  let hi := fin5.map fun k => ToRat.toRat (R.E.sup k)
  let G := (List.finRange R.h).toArray.map fun j => fin5.map fun k => ToRat.toRat (R.G j k)
  let D := Nat.lcm (aux_lcmDen (c ++ lo ++ hi)) (G.foldl (fun d g => Nat.lcm d (aux_lcmDen g)) 1)
  let s := aux_scaleTo D
  -- over `2 D`: the centre `2c + lo + hi`, the generators `2 g_j` and `(hi - lo) e_k`
  let centre := idx.map fun k => 2 * s (c.getD k 0) + s (lo.getD k 0) + s (hi.getD k 0)
  let gR := G.map fun g => aux_apply ci (g.map fun x => 2 * s x)
  let gE := idx.filterMap fun k =>
    let r := s (hi.getD k 0) - s (lo.getD k 0)
    if r = 0 then none else some (aux_apply ci (idx.map fun i => if i = k then r else 0))
  { den := 2 * D * dC, c := aux_apply ci centre
    gens := (gR ++ gE).filter fun (a, b) => a ≠ 0 ∨ b ≠ 0 }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
