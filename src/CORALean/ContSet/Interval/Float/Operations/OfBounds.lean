import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.LinProg.Float.API

/-!
# `Interval.ofBounds`, over a floating-point scalar

A box read off `2n` certified float bounds, one per coordinate direction, the
lower ones arriving against `-eⱼ`. Nothing rounds: each bound was already
rounded outward where it was computed, and negating a float is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {S : Set (Vec ℝ n)}

def Interval.ofBounds (up : ∀ j, FloatBound 𝕋 S (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 S (-LinearMap.proj j)) : Interval 𝕋 n where
  inf := fun j => neg (lo j).val
  sup := fun j => (up j).val

theorem Interval.subset_ofBounds (up : ∀ j, FloatBound 𝕋 S (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 S (-LinearMap.proj j)) :
    S ⊆ (Interval.ofBounds up lo).construct := by
  intro x hx j
  constructor
  · have h : -(x j) ≤ toReal (lo j).val := (lo j).le x hx
    show toReal (neg (lo j).val) ≤ x j
    rw [toReal_neg]
    linarith
  · exact (up j).le x hx

/-- A box answers a coordinate direction with its own bound, exactly. Every
representation carrying an ambient error box charges its rounding through
these. -/
def Interval.boundProj (I : Interval 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 I.construct (LinearMap.proj j) :=
  ⟨I.sup j, fun _ hx => (hx j).2⟩

def Interval.boundNegProj (I : Interval 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 I.construct (-LinearMap.proj j) :=
  ⟨neg (I.inf j), fun x hx => by
    -- ascribed, `linarith` reading membership no further than reducible defeq
    have h : toReal (I.inf j) ≤ x j := (hx j).1
    show -(x j) ≤ toReal (neg (I.inf j))
    rw [toReal_neg]
    linarith⟩

/-- A box answers an arbitrary direction too: a linear function of one
coordinate is largest at one end of its range, so each term is bounded by
whichever endpoint the sign picks, and the terms are summed upward.

The direction arrives as a float vector plus the fact that it denotes the dot
product with it, which a matrix row satisfies by `rfl`. -/
def Interval.boundDot (I : Interval 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 I.construct c where
  val := sumUp fun j => maximum (mulUp (a j) (I.sup j)) (mulUp (a j) (I.inf j))
  le x hx := by
    rw [hc x]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    have hlo : toReal (I.inf j) ≤ x j := (hx j).1
    have hhi : x j ≤ toReal (I.sup j) := (hx j).2
    rw [toReal_maximum]
    rcases le_total 0 (toReal (a j)) with hs | hs
    · refine le_trans ?_ (le_max_left _ _)
      exact le_trans (mul_le_mul_of_nonneg_left hhi hs) (mul_le_mulUp _ _)
    · refine le_trans ?_ (le_max_right _ _)
      exact le_trans (mul_le_mul_of_nonpos_left hlo hs) (mul_le_mulUp _ _)

end CORALean.Float
