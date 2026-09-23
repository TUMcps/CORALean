import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.NN.Layer

/-!
# The linear layer

CORA's `nnLinearLayer`: `x ↦ W x + b`. The only layer whose propagation is a set
operation and nothing else — `mtimes` for the weights, `plus` with the bias —
and so the only standard one that loses nothing at a representation closed under
both.

The bias enters as a box of zero width rather than through an operation of its
own, which is why `OfInterval` is asked for here and not a translation: a
representation that can absorb a box can absorb a point.

`Layer.linearWithError` is CORA's adaptation `W h + b ⊕ E` for a network already
carrying an approximation error. `E` need not be centred at `0` — a
neuron-merging error rarely is — so the layer commits to `E`'s own centre as its
nominal value and pays the rest into `enclose`, the way `Layer.activation`
pays a relaxation's error; `E.IsNonempty` is what puts that centre inside `E`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n m : ℕ}

def Layer.linear (W : Mat ℝ m n) (b : Vec ℝ m) : Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Interval.point b))

theorem Layer.linear_sound (W : Mat ℝ m n) (b : Vec ℝ m) :
    (Layer.linear (S := S) W b).Sound (fun x => W *ᵥ x + b) :=
  ⟨fun s _x hx => plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ (Interval.mem_point b)))⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` with an added error box `E`, CORA's `W h + b ⊕ E`. -/
def Layer.linearWithError (W : Mat ℝ m n) (b : Vec ℝ m) (E : Interval (Vec ℝ m)) :
    Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E))

/-- The value committed to is `E`'s own centre, which is why `E` has to be
nonempty: an empty box has a centre no point of it. -/
theorem Layer.linearWithError_sound (W : Mat ℝ m n) (b : Vec ℝ m) (E : Interval (Vec ℝ m))
    (hE : E.IsNonempty) :
    (Layer.linearWithError (S := S) W b E).Sound
      (fun x => W *ᵥ x + b + E.center) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox : b + E.center ∈ construct (Interval.plus (Interval.point b) E) :=
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b)
      (Interval.mem_center E hE))
  show W *ᵥ x + b + E.center ∈ construct
      (plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E)))
  rw [add_assoc]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hbox))

/-- What the layer encloses at *every* value of the error, not only its centre:
`W x + c` for any `c` within `E` of `b`, CORA's `W h + b ⊕ E` read pointwise. -/
theorem Layer.linearWithError_mem (W : Mat ℝ m n) {b c : Vec ℝ m} {E : Interval (Vec ℝ m)}
    (hc : c - b ∈ Interval.construct E) (s : S n) {x : Vec ℝ n} (hx : x ∈ construct s) :
    W *ᵥ x + c ∈
      construct ((Layer.linearWithError (S := S) W b E).enclose s) := by -- --- PROOF ---
  have hbox : b + (c - b) ∈ construct (Interval.plus (Interval.point b) E) :=
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b) hc)
  rw [add_sub_cancel] at hbox
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hbox))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
