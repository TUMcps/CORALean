import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.SetIntersection.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Theorems.CenterMemConstruct
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# An intersection of float zonotopes, operated on branch-wise

A `SetIntersection` keeps a list of members and denotes their intersection. Here the members are
the float zonotopes at `Dyadic 53` of a square `[-1, 1]²` and a diamond `|x| + |y| ≤ 3/2`, so the
set is the octagon they share, with no single zonotope denoting it. `plus`, `mtimes` and `reduce`
run on it as on any `ContSet`, each mapping the member's own float operation over the branches (a
Minkowski sum pairs every branch of one operand with every branch of the other). Every one is
outer: `SetIntersection.plus_outer`, `mtimes_outer` and `reduce_outer` are applied to these
operands, never equalities. The point `0`, a member of both branches, is carried through `plus`.

## Inputs
* none

## Output
* unit square as a float zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.SetIntersectionFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic Pointwise Matrix

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _

/-- A scalar read through `Float`, for printing. -/
def toF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- The hull of a zonotope, as `(lo₁, hi₁), (lo₂, hi₂)`. -/
def hull (Z : Zonotope (Vec D 2)) : (Float × Float) × (Float × Float) :=
  let I := Z.interval
  ((toF (I.inf 0), toF (I.sup 0)), (toF (I.inf 1), toF (I.sup 1)))


-- =====================================  MAIN DEFINITION  ====================================== --

def square : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def diamond : Zonotope (Vec D 2) :=
    ⟨2, ![d 0 0, d 0 0], ![![d 3 (-2), d 3 (-2)], ![d 3 (-2), d (-3) (-2)]], box0⟩

/-- `square ∩ diamond`. -/
def I : SetIntersection (Zonotope (Vec D 2)) := ⟨[square, diamond]⟩

/-- A segment `[-1/2, 1/2] × {0}`, intersected with the square. -/
def segment : Zonotope (Vec D 2) := ⟨1, ![d 0 0, d 0 0], ![![d 1 (-1), d 0 0]], box0⟩
def J : SetIntersection (Zonotope (Vec D 2)) := ⟨[segment, square]⟩

def sum : SetIntersection (Zonotope (Vec D 2)) := Plus.plus I J
def image : SetIntersection (Zonotope (Vec D 2)) :=
  Mtimes.mtimes (S := fun n => SetIntersection (Zonotope (Vec D n))) (𝕄 := Mat D)
    (identityMat D 2) I
def small : SetIntersection (Zonotope (Vec D 2)) := Reduce.reduce I 1

#eval sum.sets.length      -- 4 branches: every pair
#eval sum.sets.map hull
#eval image.sets.map hull  -- the identity image
#eval small.sets.map hull


/-! ## What the branch-wise operations guarantee -/

/-- The Minkowski sum of the intersections lies in every pairwise sum. -/
theorem sum_outer : ContSet.construct I + ContSet.construct J ⊆ ContSet.construct sum :=
  SetIntersection.plus_outer I J

/-- The linear image of the intersection lies in the intersection of the images. -/
theorem image_outer :
    (⋃ A ∈ ContSet.construct (identityMat D 2), (A *ᵥ ·) '' ContSet.construct I) ⊆
      ContSet.construct image :=
  SetIntersection.mtimes_outer (S := 𝒵[D]) (𝕄 := Mat D) (identityMat D 2) I

/-- The reduced branches still contain the intersection. -/
theorem small_outer : ContSet.construct I ⊆ ContSet.construct small :=
  SetIntersection.reduce_outer I 1

/-- The center of a zonotope with no error is one of its points. -/
theorem center_mem (Z : Zonotope (Vec D 2)) (h : Z.I_error = box0) : toRealVec Z.c ∈ Z.construct :=
  Zonotope.center_mem_construct Z fun i => by simp only [h, box0, toReal_d]; norm_num

/-- The origin is in the square and the diamond, hence in `I`. -/
theorem origin_mem_I : toRealVec square.c ∈ ContSet.construct I := by -- --- PROOF ---
  refine SetIntersection.mem_construct.mpr fun s hs => ?_
  simp only [I, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact center_mem _ rfl
  · have : toRealVec square.c = toRealVec diamond.c := rfl
    rw [this]; exact center_mem _ rfl

/-- The origin is in `I` and in `J`, so `0 + 0` is in `I + J`, and by `sum_outer` in `sum`. -/
theorem origin_add_origin_mem_sum :
    toRealVec square.c + toRealVec square.c ∈ ContSet.construct sum := by -- --- PROOF ---
  refine sum_outer (Set.add_mem_add origin_mem_I ?_)
  refine SetIntersection.mem_construct.mpr fun s hs => ?_
  simp only [J, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have : toRealVec square.c = toRealVec segment.c := rfl
    rw [this]; exact center_mem _ rfl
  · exact center_mem _ rfl

end CORALean.Examples.SetIntersectionFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
