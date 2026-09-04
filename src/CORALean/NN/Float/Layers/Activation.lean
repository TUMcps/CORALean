import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.NN.Layer

/-!
# Activation layers over a floating-point scalar

The exact layer's `Relaxation` with `ℝ → ℝ → ℝ` replaced by `𝕋 → 𝕋 → 𝕋`, and the
same three fields. `sound` is unchanged in shape, which is why the float layer is
cheap here: it states an *inequality* against `error` rather than an equation, so
a slope and an offset computed in floating point are sound as they stand and only
`error` has to grow. There is no refinement lemma and no `_outer_refines`
composition.

So nothing constrains `slope` and `offset` at all. They may be rounded either
way, clamped, or picked by an unverified search; the error is what pays, measured
against the values actually stored.

`Layer.activation` rounds in exactly one place: `Relaxation.box` widens
`offset ± error` outward. The slope matrix is stored exactly, and the propagation
rounds inside `mtimes` and `plus`, which charge it to the representation's own
error box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix Pointwise ContSet Plus Mtimes IntervalOuter OfInterval FloatOps
  SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ} {σ : ℝ → ℝ}

/-- An affine enclosure of `σ` on every box the stored floats describe. The
bounds arrive in `𝕋` and the argument stays real: what the layer encloses is the
exact function, whatever precision it computes the enclosure in. -/
structure Relaxation (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (σ : ℝ → ℝ) where
  slope : 𝕋 → 𝕋 → 𝕋
  offset : 𝕋 → 𝕋 → 𝕋
  error : 𝕋 → 𝕋 → 𝕋
  sound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - (toReal (slope l u) * t + toReal (offset l u))| ≤ toReal (error l u)

/-- A machine enclosure of `σ` at a stored float, which is what a slope-zero
relaxation needs. `FloatOps` evaluates no transcendental function, so this is
where one arrives — `Global/Float/Exp` builds a directed exponential. -/
structure Enclosure (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (σ : ℝ → ℝ) where
  lo : 𝕋 → 𝕋
  hi : 𝕋 → 𝕋
  lo_le (a : 𝕋) : toReal (lo a) ≤ σ (toReal a)
  le_hi (a : 𝕋) : σ (toReal a) ≤ toReal (hi a)

/-- The offset such a relaxation stores. Any float in the range would be sound —
the error below is measured from whichever one is written down — so the midpoint
is a precision choice and its rounding costs nothing. -/
def Enclosure.mid (E : Enclosure 𝕋 σ) (l u : 𝕋) : 𝕋 := half (addUp (E.lo l) (E.hi u))

/-- An offset chosen freely and the distance to each end rounded up: the shape
every slope-zero relaxation takes, and the reason the offset never has to be
rounded in a particular direction. -/
theorem aux_abs_sub_le_spread {lo hi c : 𝕋} {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    |y - toReal c| ≤ toReal (maximum (subUp hi c) (subUp c lo)) := by
  have hA := sub_le_subUp hi c
  have hB := sub_le_subUp c lo
  have hmA := le_max_left (toReal (subUp hi c)) (toReal (subUp c lo))
  have hmB := le_max_right (toReal (subUp hi c)) (toReal (subUp c lo))
  rw [toReal_maximum, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Monotonicity and nothing else, as over ℝ: the function's range over the box,
optimal at slope zero for the same reason. Unlike over ℝ it needs the endpoint
values handed to it, `FloatOps` having no transcendental function. -/
def Relaxation.ofMonotone (hσ : Monotone σ) (E : Enclosure 𝕋 σ) : Relaxation 𝕋 σ where
  slope _ _ := zero
  offset := E.mid
  error l u := maximum (subUp (E.hi u) (E.mid l u)) (subUp (E.mid l u) (E.lo l))
  sound {l u t} hl hu := by
    have hlo : toReal (E.lo l) ≤ σ t := le_trans (E.lo_le l) (hσ hl)
    have hhi : σ t ≤ toReal (E.hi u) := le_trans (hσ hu) (E.le_hi u)
    have h := aux_abs_sub_le_spread (c := E.mid l u) hlo hhi
    rw [toReal_zero, zero_mul, zero_add]
    exact h

/-- The box each neuron's deviation from its affine map is confined to, widened
outward — the one place the layer itself rounds. -/
def Relaxation.box (R : Relaxation 𝕋 σ) (I : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => subDown (R.offset (I.inf i) (I.sup i)) (R.error (I.inf i) (I.sup i))
  sup := fun i => addUp (R.offset (I.inf i) (I.sup i)) (R.error (I.inf i) (I.sup i))

/-- The affine map the relaxation chose, as a matrix, so that `mtimes` carries
it. Stored exactly: the slopes are floats already, and `diagonalBlock` only
places them. -/
def Relaxation.slopeMat (R : Relaxation 𝕋 σ) (I : Interval 𝕋 n) : Mat 𝕋 n n :=
  diagonalBlock fun i => R.slope (I.inf i) (I.sup i)

def Layer.activation (R : Relaxation 𝕋 σ) : Real.Layer S n n where
  eval x := fun i => σ (x i)
  propagate s := plus (mtimes (R.slopeMat (interval s)) s) (ofInterval (R.box (interval s)))
  propagate_outer s x hx := by
    have hbox := interval_outer s hx
    set J := interval s with hJ
    set A : Mat ℝ n n := Scalar.toRealMat (R.slopeMat J) with hA
    have hslope : ∀ i, (A *ᵥ x) i = toReal (R.slope (J.inf i) (J.sup i)) * x i := by
      intro i
      have hdiag : A = Matrix.diagonal (toRealVec fun i => R.slope (J.inf i) (J.sup i)) := by
        funext p q
        exact toReal_diagonalBlock _ p q
      rw [hdiag]
      exact Matrix.mulVec_diagonal _ _ i
    -- the deviation from the chosen affine map, which is what the box holds
    set d : Vec ℝ n := fun i => σ (x i) - (A *ᵥ x) i with hd
    have hsplit : (fun i => σ (x i)) = A *ᵥ x + d := by
      funext i
      show σ (x i) = (A *ᵥ x) i + d i
      rw [hd]
      ring
    -- and the deviation is inside the box, `sound` bounding it and the rounding widening it
    have hmem : d ∈ Interval.construct (R.box J) := by
      intro i
      have hlo : toReal (J.inf i) ≤ x i := (hbox i).1
      have hhi : x i ≤ toReal (J.sup i) := (hbox i).2
      have hrel := abs_le.mp (R.sound hlo hhi)
      have hval : d i = σ (x i) - toReal (R.slope (J.inf i) (J.sup i)) * x i := by
        show σ (x i) - (A *ᵥ x) i = _
        rw [hslope i]
      -- `sound` is an absolute value, and `subDown`/`addUp` widen its two ends outward
      have hlow : toReal (subDown (R.offset (J.inf i) (J.sup i))
          (R.error (J.inf i) (J.sup i))) ≤ d i := by
        have h := subDown_le_sub (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
        rw [hval]
        linarith [hrel.1]
      have hhigh : d i ≤ toReal (addUp (R.offset (J.inf i) (J.sup i))
          (R.error (J.inf i) (J.sup i))) := by
        have h := add_le_addUp (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
        rw [hval]
        linarith [hrel.2]
      exact ⟨hlow, hhigh⟩
    rw [hsplit]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer _ s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hmem))

end CORALean.Float
