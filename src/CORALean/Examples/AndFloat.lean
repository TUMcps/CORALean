import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.EmptySet.Real.Theorems.AndExact
import CORALean.ContSet.Fullspace.Real.Theorems.Basic
import CORALean.ContSet.LevelSet.Float.Theorems.ContainsPointSound
import CORALean.ContSet.LevelSet.Real.Theorems.AndExact
import CORALean.ContSet.Polygon.Float.Theorems.AndOuter
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Theorems.AndOuter
import CORALean.ContSet.Zonotope.Float.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef

/-!
# The `and_` family, run and applied

CORA's `and_` (set intersection) at five representations, each with its own guarantee.

* `Zonotope.and_` at `Dyadic 53`: a square `[-1, 1]²` and a diamond `|x| + |y| ≤ 2`, intersected
  through constrained zonotopes and enclosed again by a zonotope. The hull of the answer is
  printed; `Zonotope.and_outer` says the intersection lies inside it, and the origin, a point
  of both, is shown to be in the answer.
* `Polygon.and`: every pair of pieces intersected by the float `VPolytope.intersection` (through
  the pieces' boxes). A square and a triangle give one piece, printed as its box (the float box
  of a vertex list is the hull of the vertices, here `[1, 2]²`);
  `Polygon.and_outer` says the intersection of the polygons lies inside the answer.
* `LevelSet.and_`: the constraints stacked. The disc `x² + y² ≤ 1` and the open half-plane
  `-x < 0` give a level set with two rows, exactly their intersection (`LevelSet.and_exact`); a
  float sign test (`containsPoint`) certifies `(1/2, 1/4)` in the stack.
* `EmptySet.and_` and `Fullspace.and_`: `∅ ∩ s = ∅` and `univ ∩ s = s` for a set `s` of any
  representation (here a float zonotope), exactly (`EmptySet.and_exact`, `Fullspace.and_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.AndFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _

/-- A scalar read through `Float`, for printing. -/
def toF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- A box as `(lo₁, hi₁), (lo₂, hi₂)`. -/
def boxF (I : Interval (Vec D 2)) : (Float × Float) × (Float × Float) :=
  ((toF (I.inf 0), toF (I.sup 0)), (toF (I.inf 1), toF (I.sup 1)))


-- =====================================  MAIN DEFINITION  ====================================== --

/-! ## `Zonotope.and_` -/

/-- The square `[-1, 1]²` and the diamond `|x| + |y| ≤ 2`, both centred at the origin. -/
def square : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def diamond : Zonotope (Vec D 2) :=
    ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 1 0], ![d 1 0, d (-1) 0]], box0⟩

def squareDiamond : Zonotope (Vec D 2) := square.and_ diamond

#eval squareDiamond.h
#eval boxF squareDiamond.interval   -- the hull of the answer

/-- Both zonotopes have no error, so their centres are points of them. -/
theorem centre_mem (Z : Zonotope (Vec D 2)) (h : Z.I_error = box0) : toRealVec Z.c ∈ Z.construct :=
  Zonotope.centre_mem_construct Z fun i => by simp only [h, box0, toReal_d]; norm_num

/-- The origin is in both, hence in the answer. -/
theorem origin_mem : toRealVec square.c ∈ squareDiamond.construct :=
  Zonotope.and_outer square diamond ⟨centre_mem square rfl, by
    have : toRealVec square.c = toRealVec diamond.c := rfl
    rw [this]; exact centre_mem diamond rfl⟩

/-- Everything in both lies in the answer. -/
theorem squareDiamond_outer : square.construct ∩ diamond.construct ⊆ squareDiamond.construct :=
  Zonotope.and_outer square diamond


/-! ## `Polygon.and` -/

/-- A vertex list with no rounding error. -/
def poly (h : ℕ) (V : Fin h → Vec D 2) : VPolytope (Vec D 2) := ⟨h, V, box0⟩

/-- The square `[0, 2]²` and a triangle with corners `(1, 1)`, `(3, 1)`, `(1, 3)`. -/
def P : Polygon D :=
  ⟨[poly 4 ![![d 0 0, d 0 0], ![d 2 0, d 0 0], ![d 2 0, d 2 0], ![d 0 0, d 2 0]]]⟩
def Q : Polygon D := ⟨[poly 3 ![![d 1 0, d 1 0], ![d 3 0, d 1 0], ![d 1 0, d 3 0]]]⟩

def PQ : Polygon D := Polygon.and P Q

#eval PQ.sets.length                          -- 1 piece
#eval PQ.sets.map fun V => boxF V.interval    -- its box, [1, 2]²

theorem PQ_outer : ContSet.construct P ∩ ContSet.construct Q ⊆ ContSet.construct PQ :=
  Polygon.and_outer P Q


/-! ## `LevelSet.and_`, `EmptySet.and_`, `Fullspace.and_` -/

/-- The disc `x² + y² - 1 ≤ 0`. -/
noncomputable def andDisc : Real.LevelSet 2 where
  m := 1
  f x := ![x 0 ^ 2 + x 1 ^ 2 - 1]
  op := ![.le]

/-- The open half-plane `-x < 0`. -/
noncomputable def andHalf : Real.LevelSet 2 where
  m := 1
  f x := ![-x 0]
  op := ![.lt]

/-- The two stacked: `x² + y² ≤ 1` and `x > 0`, exactly the intersection. -/
theorem stack_exact : (andDisc.and_ andHalf).construct = andDisc.construct ∩ andHalf.construct :=
  Real.LevelSet.and_exact andDisc andHalf

/-- The stack with its functions dropped, which the sign test never calls, so it can run. -/
def stackOps : Real.LevelSet 2 :=
  Real.LevelSet.and_ ⟨1, fun _ => 0, ![.le]⟩ ⟨1, fun _ => 0, ![.lt]⟩

/-- Row values at `(1/2, 1/4)`: `-11/16` and `-1/2`, exactly. -/
def Bp : Fin 2 → D × D := ![(d (-11) (-4), d (-11) (-4)), (d (-1) (-1), d (-1) (-1))]

#eval LevelSet.containsPoint (𝕋 := D) stackOps Bp   -- true

set_option maxRecDepth 4096 in
/-- `(1/2, 1/4)` is in the stack, by the float sign test. -/
theorem stack_mem :
    (![1 / 2, 1 / 4] : Vec ℝ 2) ∈ (andDisc.and_ andHalf).construct := by -- --- PROOF ---
  -- the sign test is `true` by evaluation; the bounds are the exact row values
  refine LevelSet.containsPoint_sound (𝕋 := D) (andDisc.and_ andHalf) Bp _ ?_ rfl
  intro i
  fin_cases i
  · simp [Real.LevelSet.and_, andDisc, andHalf, Bp, Fin.append, Fin.addCases, toReal_d]
    norm_num
  · simp [Real.LevelSet.and_, andDisc, andHalf, Bp, Fin.append, Fin.addCases, toReal_d]

/-- `∅ ∩ s = ∅`, for a float zonotope `s`. -/
example (E : Real.EmptySet 2) :
    ContSet.construct (E.and_ square) = ContSet.construct E ∩ ContSet.construct square :=
  Real.EmptySet.and_exact E square

/-- `univ ∩ s = s`, for a float zonotope `s`. -/
example (F : Real.Fullspace 2) :
    ContSet.construct (F.and_ square) = F.construct ∩ ContSet.construct square :=
  Real.Fullspace.and_exact F square

end CORALean.Examples.AndFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
