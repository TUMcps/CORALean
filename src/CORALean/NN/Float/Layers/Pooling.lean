import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.NN.Float.Layers.Convolution
import CORALean.NN.Layers.Pooling

/-!
# The pooling layers over a floating-point scalar

`1 / k` is not a float, so average pooling's weight cannot be computed here and
is a parameter. The layer encloses the map that weight denotes, which is
averaging only as closely as the weight is `1 / k` — the status a stored weight
matrix has. Where it matters it is exact: for a window of `2 ^ d` taps the weight
is `half` iterated `d` times from `one`, and every pooling window CORA builds is
of that shape.

Max pooling rounds one number. The pivot is a choice and never a correctness
condition, exactly as `ReLU`'s slope is, so `pivot` may read `le`, which
`SoundFloatArithmetic` constrains in no way. What rounds is the gap, and it
rounds up — `subUp` per tap and an exact `maximumOver` above them, whose floor at
`zero` is what the exact layer spends an `if` on.

`Real.maxPool_bounds` is reused unchanged, having been stated for an arbitrary
`g` bounding the window.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

-- `Matrix` unscoped would make `FloatOps.zero` ambiguous; only `*ᵥ` is wanted
open scoped Matrix
open Pointwise ContSet Plus Mtimes IntervalOuter OfInterval FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋] {n m k : ℕ}

/-! ## Average pooling -/

def Layer.avgPool (winv : 𝕋) (tap : Fin m → Fin k → Fin n) : Real.Layer S n m :=
  Layer.linear (tapMat tap fun _ _ => winv) fun _ => zero

theorem Layer.avgPool_eval (winv : 𝕋) (tap : Fin m → Fin k → Fin n)
    (htap : ∀ j, Function.Injective (tap j)) (x : Vec ℝ n) (j : Fin m) :
    (Layer.avgPool (S := S) winv tap).eval x j = toReal winv * ∑ l, x (tap j l) := by
  show (toRealMat (tapMat tap fun _ _ => winv) *ᵥ x) j + toRealVec (fun _ => zero) j = _
  rw [toRealMat_tapMat, Real.tapMat_mulVec _ _ htap, ← Finset.mul_sum]
  show toReal winv * (∑ l, x (tap j l)) + toReal (zero : 𝕋) = _
  rw [toReal_zero, add_zero]

/-! ## Max pooling -/

variable [IntervalOuter S 𝕋]

/-- One `1` per row, placed rather than computed, so it denotes the exact
layer's selection matrix entry for entry. -/
def selectMat (sel : Fin m → Fin n) : Mat 𝕋 m n :=
  tapMat (fun (j : Fin m) (_ : Fin 1) => sel j) fun _ _ => one

theorem selectMat_mulVec (sel : Fin m → Fin n) (x : Vec ℝ n) (j : Fin m) :
    (toRealMat (selectMat (𝕋 := 𝕋) sel) *ᵥ x) j = x (sel j) := by -- --- PROOF ---
  show ((toRealMat (tapMat (fun (j : Fin m) (_ : Fin 1) => sel j) fun _ _ => (one : 𝕋)))
    *ᵥ x) j = _
  rw [toRealMat_tapMat, Real.tapMat_mulVec _ _ fun _ a b _ => Subsingleton.elim a b,
    Fin.sum_univ_one]
  show toReal (one : 𝕋) * x (sel j) = _
  rw [toReal_one, one_mul]

/-- Zero at the pivot, so the maximum is floored there and a stable window still
gets a gap of exactly zero; every other tap rounds its reach up. -/
def maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval 𝕋 n) (j : Fin m) : 𝕋 :=
  maximumOver fun l =>
    if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))

/-- Read at the pivot, where the window contributes an exact `zero`. -/
theorem maxPoolGapUp_nonneg (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval 𝕋 n) (j : Fin m) : 0 ≤ toReal (maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) (p j)
  rw [if_pos rfl, toReal_zero] at h
  exact h

/-- And at any other tap, where `subUp` is the one rounding this layer pays. -/
theorem le_maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval 𝕋 n) (j : Fin m) {l : Fin (k + 1)} (hl : l ≠ p j) :
    toReal (I.sup (tap j l)) - toReal (I.inf (tap j (p j)))
      ≤ toReal (maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) l
  rw [if_neg hl] at h
  exact le_trans (sub_le_subUp _ _) h


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Layer.maxPool (tap : Fin m → Fin (k + 1) → Fin n)
    (pivot : Interval 𝕋 n → Fin m → Fin (k + 1)) : Real.Layer S n m where
  eval x := fun j => Real.windowMax fun l => x (tap j l)
  enclose s :=
    plus (mtimes (selectMat fun j => tap j (pivot (interval s) j)) s)
      (ofInterval ⟨fun _ => zero, maxPoolGapUp tap (pivot (interval s)) (interval s)⟩)
  enclose_outer s x hx := by
    have hbox : ∀ i, toReal ((interval s).inf i) ≤ x i ∧ x i ≤ toReal ((interval s).sup i) :=
      interval_outer s hx
    set I := interval s with hI
    set p := pivot I with hp
    set A : Mat ℝ m n := Scalar.toRealMat (selectMat (𝕋 := 𝕋) fun j => tap j (p j)) with hA
    -- what the pivot misses, which is what the box holds
    set d : Vec ℝ m := fun j => Real.windowMax (fun l => x (tap j l)) - x (tap j (p j))
      with hd
    have hsplit : (fun j => Real.windowMax fun l => x (tap j l)) = A *ᵥ x + d := by
      funext j
      have hsel : (A *ᵥ x) j = x (tap j (p j)) := by
        rw [hA]
        exact selectMat_mulVec (fun j => tap j (p j)) x j
      show Real.windowMax (fun l => x (tap j l)) = (A *ᵥ x) j + d j
      rw [hsel, hd]
      ring
    -- the exact layer's bound, at the rounded-up gap it was stated for
    have hmem : d ∈ Interval.construct
        (⟨fun _ => zero, maxPoolGapUp tap p I⟩ : Interval 𝕋 m) := by
      intro j
      have h := Real.maxPool_bounds (tap j) (p j) (toRealVec I.inf) (toRealVec I.sup) x hbox
        (maxPoolGapUp_nonneg tap p I j) fun l hl => le_maxPoolGapUp tap p I j hl
      have hz : toReal (zero : 𝕋) ≤ d j := by
        rw [toReal_zero]
        exact h.1
      exact ⟨hz, h.2⟩
    have hA' : A ∈ ContSet.construct (selectMat (𝕋 := 𝕋) fun j => tap j (p j)) := by
      rw [ContSet.construct_mat]
      exact hA
    rw [hsplit]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer _ s (Set.mem_biUnion hA' (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hmem))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
