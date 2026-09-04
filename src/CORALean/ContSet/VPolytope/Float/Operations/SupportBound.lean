import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.InflatedContSet.Operations.Bound

/-!
# A float vertex description answers a coordinate direction

The exact layer's answer is a maximum over the vertex list, so this layer's is
`maximumOver` — no certificate, no rounding, the maximum of stored floats being
one of them. The error box adds its own reach, and the two are added upward.

Coordinate directions only. A general direction would need the vertices scored
against it, which is a dot product per vertex and a rounding per dot product;
what every operation here actually asks for is `±eⱼ`, and a minimum in direction
`-eⱼ` is `maximumOver` of the negated row, so no `minimumOver` is needed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.nominalBoundProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 (nominalSet P) (LinearMap.proj j) where
  val := maximumOver fun l => P.V j l
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le (LinearMap.proj j)
      (fun l => le_maximumOver (fun l => P.V j l) l) hx

-- the opposite direction, where the negation is taken before the maximum
def VPolytope.nominalBoundNegProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 (nominalSet P) (-LinearMap.proj j) where
  val := maximumOver fun l => neg (P.V j l)
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le (-LinearMap.proj j)
      (fun l => by
        show -(toReal (P.V j l)) ≤ toReal (maximumOver fun l => neg (P.V j l))
        rw [← toReal_neg]
        exact le_maximumOver (fun l => neg (P.V j l)) l) hx

def VPolytope.boundProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 P.construct (LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundProj j) (P.E.boundProj j)

def VPolytope.boundNegProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 P.construct (-LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundNegProj j) (P.E.boundNegProj j)

/-- A general direction, at the price the coordinate ones avoid: a rounded dot
product per vertex, then the largest of them. -/
def VPolytope.nominalBoundDot (P : VPolytope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (nominalSet P) c where
  val := maximumOver fun l => dotUp a fun j => P.V j l
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le c
      (fun l => by
        rw [hc]
        exact le_trans (le_dotUp a fun j => P.V j l)
          (le_maximumOver (fun l => dotUp a fun j => P.V j l) l)) hx

def VPolytope.boundDot (P : VPolytope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 P.construct c :=
  InflatedContSet.boundOfParts (P.nominalBoundDot a hc) (P.E.boundDot a hc)

end CORALean.Float
