import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.Layer

/-!
# Activation layers, and what an activation function has to supply

CORA's `nnActivationLayer`: the same scalar function applied to every neuron.
No representation is closed under one, so every activation layer is an
enclosure, and a `Relaxation` is what makes it a sound one — per neuron, an
affine map and a bound on how far the function departs from it over that
neuron's own input range.

The slope is what distinguishes this from interval arithmetic. Propagating
`diag(λ)` through the set keeps the neurons' dependence on the input, and only
the leftover deviation is thrown into a box; taking `λ = 0` is legal, and is
exactly the point where that dependence is lost. So an activation layer is where
all of a network's precision is decided, and the `Relaxation` is the whole of
that decision.

The relaxation is a function of the input bounds because it has to be: ReLU has
no affine enclosure with a finite error on all of ℝ. That is why this layer
needs `IntervalOuter` and the linear one does not.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

/-- An affine enclosure of `σ` on every interval, as CORA's activation layers
compute one before they propagate anything. -/
structure Relaxation (σ : ℝ → ℝ) where
  slope : ℝ → ℝ → ℝ
  offset : ℝ → ℝ → ℝ
  error : ℝ → ℝ → ℝ
  sound {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    |σ t - (slope l u * t + offset l u)| ≤ error l u

/-- Nothing but monotonicity: the function's range over the box, which is what
interval arithmetic gives and carries no slope. Optimal at `λ = 0`, since a
monotone function alone admits no better — the range of `σ t - λ t` only widens
as `λ` moves away from zero. -/
noncomputable def Relaxation.ofMonotone {σ : ℝ → ℝ} (hσ : Monotone σ) : Relaxation σ where
  slope _ _ := 0
  offset l u := (σ l + σ u) / 2
  error l u := (σ u - σ l) / 2
  sound hl hu := by
    rw [abs_le]
    exact ⟨by linarith [hσ hl], by linarith [hσ hu]⟩

/-- The box each neuron's deviation from its affine map is confined to. -/
def Relaxation.box {σ : ℝ → ℝ} (R : Relaxation σ) (I : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) where
  inf := fun i => R.offset (I.inf i) (I.sup i) - R.error (I.inf i) (I.sup i)
  sup := fun i => R.offset (I.inf i) (I.sup i) + R.error (I.inf i) (I.sup i)

/-- The affine map the relaxation chose, as a matrix, so that `mtimes` carries
it and the neurons' dependence on the input survives. -/
def Relaxation.slopeMat {σ : ℝ → ℝ} (R : Relaxation σ) (I : Interval (Vec ℝ n)) :
    Mat ℝ n n :=
  Matrix.diagonal fun i => R.slope (I.inf i) (I.sup i)

def Layer.activation {σ : ℝ → ℝ} (R : Relaxation σ) : Layer S n n where
  eval x := fun i => σ (x i)
  propagate s := plus (mtimes (R.slopeMat (interval s)) s) (ofInterval (R.box (interval s)))
  propagate_outer s x hx := by
    have hbox := interval_outer s hx
    -- the deviation from the chosen affine map, which is what the box holds
    set d : Vec ℝ n := fun i => σ (x i) - (R.slopeMat (interval s) *ᵥ x) i with hd
    have hslope : ∀ i, (R.slopeMat (interval s) *ᵥ x) i
        = R.slope ((interval s).inf i) ((interval s).sup i) * x i := fun i =>
      Matrix.mulVec_diagonal _ _ i
    have hsplit : (fun i => σ (x i)) = R.slopeMat (interval s) *ᵥ x + d := by
      funext i
      show σ (x i) = (R.slopeMat (interval s) *ᵥ x) i + d i
      rw [hd]
      ring
    have hmem : d ∈ construct (R.box (interval s)) := by
      intro i
      have hlo : (interval s).inf i ≤ x i := (hbox i).1
      have hhi : x i ≤ (interval s).sup i := (hbox i).2
      have hrel := abs_le.mp (R.sound hlo hhi)
      have hval : d i = σ (x i)
          - R.slope ((interval s).inf i) ((interval s).sup i) * x i := by
        show σ (x i) - (R.slopeMat (interval s) *ᵥ x) i = _
        rw [hslope i]
      have hlow : R.offset ((interval s).inf i) ((interval s).sup i)
          - R.error ((interval s).inf i) ((interval s).sup i) ≤ d i := by
        rw [hval]; linarith [hrel.1]
      have hhigh : d i ≤ R.offset ((interval s).inf i) ((interval s).sup i)
          + R.error ((interval s).inf i) ((interval s).sup i) := by
        rw [hval]; linarith [hrel.2]
      exact ⟨hlow, hhigh⟩
    rw [hsplit]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer _ s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hmem))

end CORALean.Real
