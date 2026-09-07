import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.Layers.Convolution

/-!
# The pooling layers

CORA's `nnAvgPool2DLayer` and `nnMaxPool2DLayer`, and they part company here.

`Layer.avgPool` is `Layer.linear` at `tapMat` with every weight `1 / k`, which is
`Layer.conv` at a constant kernel; the window is the taps, so a stride or a
channel layout never appears.

Max pooling does not fit `Relaxation` at all. A relaxation is a scalar
`σ : ℝ → ℝ` over one interval, where a pooled output is a function of `k + 1`
inputs over `k + 1` intervals; and `Layer.activation` turns slopes into
`Matrix.diagonal`, where max pooling's affine part is a *selection* matrix. What
carries over is the shape: an affine part through `mtimes` and a box for the rest.

That affine part is one input per window — the pivot — and the box is `[0, gap]`,
a maximum never being below any of its arguments. `gap` is zero exactly when the
pivot dominates the window, so a stable window makes this layer exact, and
`pivot` is precision and never soundness, as `reluSlope` is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n m k : ℕ}

/-! ## Average pooling -/

noncomputable def Layer.avgPool (tap : Fin m → Fin k → Fin n) : Layer S n m :=
  Layer.linear (tapMat tap fun _ _ => (k : ℝ)⁻¹) 0

theorem Layer.avgPool_eval (tap : Fin m → Fin k → Fin n)
    (htap : ∀ j, Function.Injective (tap j)) (x : Vec ℝ n) (j : Fin m) :
    (Layer.avgPool (S := S) tap).eval x j = (k : ℝ)⁻¹ * ∑ l, x (tap j l) := by
  show (tapMat tap (fun _ _ => (k : ℝ)⁻¹) *ᵥ x) j + (0 : Vec ℝ m) j = _
  rw [tapMat_mulVec _ _ htap, ← Finset.mul_sum]
  show _ + (0 : ℝ) = _
  ring

/-! ## Max pooling

A window's bounds are what the pivot is chosen against, so only from here on is
`IntervalOuter` needed — average pooling reads no box at all. -/

variable [IntervalOuter S]

/-- One input per output, which is the affine part a pooled window keeps. -/
def selectMat (sel : Fin m → Fin n) : Mat ℝ m n :=
  tapMat (fun (j : Fin m) (_ : Fin 1) => sel j) fun _ _ => 1

theorem selectMat_mulVec (sel : Fin m → Fin n) (x : Vec ℝ n) (j : Fin m) :
    (selectMat sel *ᵥ x) j = x (sel j) := by
  have h := tapMat_mulVec (fun (j : Fin m) (_ : Fin 1) => sel j) (fun _ _ => (1 : ℝ))
    (fun _ a b _ => Subsingleton.elim a b) x j
  rw [Fin.sum_univ_one, one_mul] at h
  exact h

/-- The largest coordinate a window reads. `k + 1` in the type is what says a
pooling window is nonempty, which is what makes a maximum exist at all. -/
noncomputable def windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem le_windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : f l ≤ windowMax f :=
  Finset.le_sup' f (Finset.mem_univ l)

theorem windowMax_le {k : ℕ} {f : Fin (k + 1) → ℝ} {c : ℝ} (h : ∀ l, f l ≤ c) :
    windowMax f ≤ c :=
  Finset.sup'_le _ f fun l _ => h l

/-- How far the window may rise above its pivot, for *any* `g` bounding what the
other taps reach above the pivot's lower bound — arbitrary, so the float layer
rounds `g` up and reuses this proof. -/
theorem maxPool_bounds {k : ℕ} (t : Fin (k + 1) → Fin n) (p : Fin (k + 1))
    (lo hi x : Vec ℝ n) (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) {g : ℝ} (hg0 : 0 ≤ g)
    (hg : ∀ l, l ≠ p → hi (t l) - lo (t p) ≤ g) :
    0 ≤ windowMax (fun l => x (t l)) - x (t p) ∧
      windowMax (fun l => x (t l)) - x (t p) ≤ g := by -- --- PROOF ---
  refine ⟨by linarith [le_windowMax (fun l => x (t l)) p], ?_⟩
  have h : windowMax (fun l => x (t l)) ≤ x (t p) + g := by
    refine windowMax_le fun l => ?_
    by_cases hl : l = p
    · rw [hl]
      linarith
    · linarith [(hx (t l)).2, (hx (t p)).1, hg l hl]
  linarith

/-- Zero at the pivot itself, so the maximum is floored at zero and a stable
window gets a gap of exactly zero. -/
noncomputable def maxPoolGap (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec ℝ n)) (j : Fin m) : ℝ :=
  windowMax fun l => if l = p j then 0 else I.sup (tap j l) - I.inf (tap j (p j))

/-- Read at the pivot itself, where the window contributes zero. -/
theorem maxPoolGap_nonneg (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec ℝ n)) (j : Fin m) : 0 ≤ maxPoolGap tap p I j := by
  have h := le_windowMax
    (fun l => if l = p j then (0 : ℝ) else I.sup (tap j l) - I.inf (tap j (p j))) (p j)
  rwa [if_pos rfl] at h

/-- And at any other tap, which is what `maxPool_bounds` asks of `g`. -/
theorem le_maxPoolGap (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec ℝ n)) (j : Fin m) {l : Fin (k + 1)} (hl : l ≠ p j) :
    I.sup (tap j l) - I.inf (tap j (p j)) ≤ maxPoolGap tap p I j := by
  have h := le_windowMax
    (fun l => if l = p j then (0 : ℝ) else I.sup (tap j l) - I.inf (tap j (p j))) l
  rwa [if_neg hl] at h


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Layer.maxPool (tap : Fin m → Fin (k + 1) → Fin n)
    (pivot : Interval (Vec ℝ n) → Fin m → Fin (k + 1)) : Layer S n m where
  eval x := fun j => windowMax fun l => x (tap j l)
  enclose s :=
    plus (mtimes (selectMat fun j => tap j (pivot (interval s) j)) s)
      (ofInterval ⟨fun _ => 0, maxPoolGap tap (pivot (interval s)) (interval s)⟩)
  enclose_outer s x hx := by
    have hbox := interval_outer s hx
    set I := interval s with hI
    set p := pivot I with hp
    set A := selectMat fun j => tap j (p j) with hA
    -- what the pivot misses, which is what the box holds
    set d : Vec ℝ m := fun j => windowMax (fun l => x (tap j l)) - x (tap j (p j)) with hd
    have hsplit : (fun j => windowMax fun l => x (tap j l)) = A *ᵥ x + d := by
      funext j
      show windowMax (fun l => x (tap j l)) = (A *ᵥ x) j + d j
      rw [hA, selectMat_mulVec, hd]
      ring
    have hmem : d ∈ Interval.construct
        (⟨fun _ => 0, maxPoolGap tap p I⟩ : Interval (Vec ℝ m)) := by
      intro j
      exact maxPool_bounds (tap j) (p j) I.inf I.sup x hbox (maxPoolGap_nonneg tap p I j)
        fun l hl => le_maxPoolGap tap p I j hl
    rw [hsplit]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer _ s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hmem))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
