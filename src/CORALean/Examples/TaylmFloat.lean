import CORALean.ContSet.Conversion.Float.Theorems.IntervalTaylmContains
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Taylm.Float.Theorems.ExpOuter
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

/-!
# A Taylor model, run and bounded

At `Dyadic 53`. The box `[1/2, 3/2] × [-1/4, 1/4]` becomes an array of two Taylor models, one
variable per coordinate (`Interval.taylm`, order 3). The product `x · y`, the sum `x · y + x`
and `exp (x · y)` are then computed in floats (`Taylm.times`, `Taylm.plus`, `Taylm.exp`), and
`Taylm.bounds` reads off the range each model guarantees, printed below as `m*2^e`.

The theorem instances apply the general ones to these models: `Interval.taylm_contains` puts the
whole box inside the models' range set, `Taylm.times_outer`, `Taylm.plus_outer` and
`Taylm.exp_outer` say the computed models enclose the product, the sum and `exp` of the
coordinate functions they came from, and `Taylm.bounds_mem` turns that into a range bound on the
normalized domain `[-1, 1]²`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.TaylmFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- A scalar as `m*2^e`. -/
def show' (x : D) : String := s!"{x.mantissa}*2^{x.exponent}"

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A converted zonotope's polynomial: the center plus the generators times the variables. -/
theorem aux_taylm_poly (Z : Zonotope (Vec D 2)) (N : ℕ) (i : Fin 2) (t : Vec ℝ Z.h) :
    (Z.taylm N i).nominal.poly t = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j := by
  -- unfold the model, then evaluate the term list
  simp only [Zonotope.taylm, Taylm.nominal, Real.Taylm.poly, List.map_cons, List.map_ofFn,
    Real.Taylm.polyOf_cons, Real.Taylm.polyOf_ofFn, Real.Taylm.monomial_zero,
    Function.comp_def, Real.Taylm.monomial_single, mul_one]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1/2, 3/2] × [-1/4, 1/4]`. -/
def box : Interval (Vec D 2) := ⟨![d 1 (-1), d (-1) (-2)], ![d 3 (-1), d 1 (-2)]⟩

/-- The two coordinate functions as models over `t ∈ [-1, 1]²`, truncation order 3. -/
def X : Taylm D 2 := (box.taylm 3) 0
def Y : Taylm D 2 := (box.taylm 3) 1

/-- `x · y`, `x · y + x`, `exp (x · y)`. -/
def XY : Taylm D 2 := X.times Y
def S : Taylm D 2 := XY.plus X
def E : Taylm D 2 := XY.exp 53

#eval X.bounds.inf |> show'    -- the range of `x`
#eval X.bounds.sup |> show'
#eval XY.bounds.inf |> show'   -- the range of `x · y`
#eval XY.bounds.sup |> show'
#eval S.bounds.inf |> show'
#eval S.bounds.sup |> show'
#eval E.bounds.inf |> show'    -- the range of `exp (x · y)`
#eval E.bounds.sup |> show'


/-! ## What the computed models guarantee -/

/-- Every point of the box is a value of the two models (some `t ∈ [-1, 1]²` and remainders). -/
theorem box_subset : box.construct ⊆ Taylm.construct (box.taylm 3) := Interval.taylm_contains box 3

/-- A converted box encloses its coordinate function: center plus generator times `t`. -/
theorem taylm_encloses (i : Fin 2) :
    ((box.taylm 3) i).Encloses fun t =>
      toReal (box.zonotope.c i) + ∑ j, toReal (box.zonotope.G j i) * t j := by -- --- PROOF ---
  intro t _
  -- the polynomial is the center plus the generators times the variables
  have h : ((box.taylm 3) i).inflated.poly t =
      toReal (box.zonotope.c i) + ∑ j, toReal (box.zonotope.G j i) * t j :=
    aux_taylm_poly box.zonotope 3 i t
  show ((box.taylm 3) i).inflated.rem.inf ≤ _ - ((box.taylm 3) i).inflated.poly t ∧
    _ - ((box.taylm 3) i).inflated.poly t ≤ ((box.taylm 3) i).inflated.rem.sup
  rw [h, sub_self]
  simp [Taylm.inflated, Interval.taylm, Zonotope.taylm, Interval.zonotope, toReal_zero]

/-- The product, the sum and `exp` enclose the functions they were computed from. -/
theorem XY_encloses : XY.Encloses fun t =>
    (toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) *
    (toReal (box.zonotope.c 1) + ∑ j, toReal (box.zonotope.G j 1) * t j) :=
  Taylm.times_outer (taylm_encloses 0) (taylm_encloses 1)

theorem S_encloses : S.Encloses fun t =>
    (toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) *
    (toReal (box.zonotope.c 1) + ∑ j, toReal (box.zonotope.G j 1) * t j) +
    (toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) :=
  Taylm.plus_outer XY_encloses (taylm_encloses 0)

set_option maxRecDepth 4096 in
/-- `exp` of the product: the precondition (the top of the hull is at most `2 ^ 52`) is a
float comparison that runs. -/
theorem E_encloses : E.Encloses fun t => Real.exp
    ((toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) *
    (toReal (box.zonotope.c 1) + ∑ j, toReal (box.zonotope.G j 1) * t j)) := by
  refine Taylm.exp_outer 53 XY_encloses ?_
  refine (toReal_le_of_le (b := d 1 52) rfl).trans ?_
  rw [toReal_d]
  norm_num

/-- Their ranges on the normalized domain, as the `bounds` the run printed. -/
theorem S_range {t : Vec ℝ 2} (ht : t ∈ Real.Taylm.box 2) :
    toReal S.bounds.inf ≤ ((toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) *
    (toReal (box.zonotope.c 1) + ∑ j, toReal (box.zonotope.G j 1) * t j) +
    (toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j)) ∧
    ((toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j) *
    (toReal (box.zonotope.c 1) + ∑ j, toReal (box.zonotope.G j 1) * t j) +
    (toReal (box.zonotope.c 0) + ∑ j, toReal (box.zonotope.G j 0) * t j)) ≤ toReal S.bounds.sup :=
  Taylm.bounds_mem S_encloses ht

end CORALean.Examples.TaylmFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
