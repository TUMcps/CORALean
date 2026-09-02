import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset

/-!
# Vertex descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isVRep` set, its vertices held in `𝕋`, plus the error box
that makes it an `InflatedContSet`.

The box is the only sound place to pay. Rounding a vertex moves a point, and
there is no direction to move it that enlarges the hull — a hull has no centre
to move away from — so what rounding costs cannot be absorbed into the vertices
the way an interval absorbs it into its bounds.

Vertices are stored as the columns of a matrix, as a zonotope's generators are,
and the nominal reading transposes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure VPolytope (𝕋 : Type) (n : ℕ) where
  k : ℕ
  V : Mat 𝕋 n k
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (VPolytope 𝕋 n) (CORALean.Real.VPolytope (Vec ℝ n)) 𝕋 n where
  nominal P := ⟨P.k, fun l i => toReal (P.V i l)⟩
  error P := P.E

/-- The nominal vertex list, so proofs can see through the instance. Through it
every count is `P.k`, where going via the instance gives the equal-but-distinct
`(nominal P).k`. -/
theorem VPolytope.nominal_eq [SoundFloatArithmetic 𝕋] (P : VPolytope 𝕋 n) :
    InflatedContSet.nominal P
      = CORALean.Real.VPolytope.mk P.k (fun l i => toReal (P.V i l)) := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev VPolytope.construct [SoundFloatArithmetic 𝕋] (P : VPolytope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

/-- A box wide enough for every column's rounding at once: the operations here
store a whole vertex list, so one box has to cover all of it. -/
def VPolytope.columnGap {k : ℕ} (lo hi : Mat 𝕋 n k) : Interval 𝕋 n :=
  ⟨fun _ => zero, fun i => maximumOver fun l => subUp (hi i l) (lo i l)⟩

/-- Storing the lower rounding of column `l` leaves a residual the gap admits. -/
theorem VPolytope.mem_columnGap [SoundFloatArithmetic 𝕋] {k : ℕ} {lo hi : Mat 𝕋 n k}
    {p : Vec ℝ n} {l : Fin k}
    (h : ∀ i, toReal (lo i l) ≤ p i ∧ p i ≤ toReal (hi i l)) :
    (fun i => p i - toReal (lo i l)) ∈ (VPolytope.columnGap lo hi).construct := by
  refine fun i => ⟨?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ p i - toReal (lo i l)
    rw [toReal_zero]
    linarith [(h i).1]
  · show p i - toReal (lo i l) ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l'))
    calc p i - toReal (lo i l)
        ≤ toReal (hi i l) - toReal (lo i l) := by linarith [(h i).2]
      _ ≤ toReal (subUp (hi i l) (lo i l)) := sub_le_subUp _ _
      _ ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l')) :=
          le_maximumOver (fun l' => subUp (hi i l') (lo i l')) l

end CORALean.Float
