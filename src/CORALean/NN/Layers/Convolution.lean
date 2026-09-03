import CORALean.NN.Layers.Linear

/-!
# The convolution layer

CORA's `nnConv2DLayer`, and the conclusion is that it is not a layer at all: a
convolution is `Layer.linear` at a particular matrix, by definition and not up
to a lemma. `Layer.conv` unfolds to `Layer.linear`, contributes no `propagate`
of its own and no soundness proof of its own; what it contributes is the matrix
and `conv_eval`, the proof that the matrix computes the convolution.

## Why the matrix, and not the structure

A convolution's weights are shared and its matrix is sparse, and neither buys
anything here. Sharing is a property of the *argument*: `tapMat` takes a weight
per output and per tap, and a convolution passes `fun j l => K (chan j) l`,
which is what "shared across positions" means. Sparsity is a property of the
arithmetic, and the arithmetic is the representation's — `mtimes` at a zonotope
costs one product per nonzero if it exploits the structure and `m · n` if it
does not, and neither changes the set. So exploiting either is an optimisation
of `Mtimes`, in the layer below this one, and the specification is finished when
it names the matrix.

## The taps

`tap j l` is the input coordinate that tap `l` of output `j` reads, which puts
padding, stride, dilation and the channel layout into one index function and
keeps them out of the layer. Everything asked of it is `Function.Injective
(tap j)`: a window reads each input at most once.

`tapEntry` is a recursion rather than `∑ l, if tap j l = i then w j l else 0`,
and the reason is the float layer. The two agree — that is `tapEntry_dot` — but
a sum of `k` terms rounds and picking the one that matches does not, so the
float matrix built this way holds the kernel's floats *exactly* as they were
read in, and the float convolution rounds nowhere, as its linear layer does not.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n m k c : ℕ}

/-- The weight one row places at input coordinate `i`: the first tap reading it,
and zero if none does. -/
def tapEntry {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Fin k → ℝ) → Fin n → ℝ
  | 0, _, _, _ => 0
  | _ + 1, t, v, i =>
    if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i

theorem tapEntry_eq_zero {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → ℝ) (i : Fin n),
      (∀ l, t l ≠ i) → tapEntry t v i = 0 := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro t v i h
    show (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i) = 0
    rw [if_neg (h 0)]
    exact ih _ _ _ fun l => h l.succ

/-- The row read against a vector is the weighted sum over the taps, which is
what makes `tapMat` the matrix of a stencil. Injectivity is where a window
reading one input twice would break it: the matrix holds one weight per entry
and the sum would hold two. -/
theorem tapEntry_dot {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → ℝ) (x : Vec ℝ n),
      Function.Injective t → ∑ i, tapEntry t v i * x i = ∑ l, v l * x (t l) := by
  intro k
  induction k with
  | zero =>
    intro t v x _
    have h0 : ∀ i : Fin n, tapEntry t v i * x i = 0 := fun i => by
      show (0:ℝ) * x i = 0
      ring
    rw [Finset.sum_congr rfl fun i _ => h0 i, Finset.sum_const_zero, Fin.sum_univ_zero]
  | succ k ih =>
    intro t v x ht
    have hz : tapEntry (fun l => t l.succ) (fun l => v l.succ) (t 0) = 0 :=
      tapEntry_eq_zero _ _ _ fun l hl => Fin.succ_ne_zero l (ht hl)
    have key : ∀ i, tapEntry t v i * x i
        = (if t 0 = i then v 0 * x i else 0)
          + tapEntry (fun l => t l.succ) (fun l => v l.succ) i * x i := by
      intro i
      show (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i) * x i
        = _
      by_cases hi : t 0 = i
      · rw [if_pos hi, if_pos hi, ← hi, hz]
        ring
      · rw [if_neg hi, if_neg hi]
        ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ (t 0) fun i => v 0 * x i,
      if_pos (Finset.mem_univ (t 0)), ih _ _ x (fun a b hab => Fin.succ_injective k (ht hab)),
      Fin.sum_univ_succ (f := fun l => v l * x (t l))]

/-- Output `j` reads inputs `tap j l` with weight `w j l`. -/
def tapMat (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → ℝ) : Mat ℝ m n :=
  fun j i => tapEntry (tap j) (w j) i

theorem tapMat_mulVec (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → ℝ)
    (htap : ∀ j, Function.Injective (tap j)) (x : Vec ℝ n) (j : Fin m) :
    (tapMat tap w *ᵥ x) j = ∑ l, w j l * x (tap j l) := by
  show ∑ i, tapEntry (tap j) (w j) i * x i = _
  exact tapEntry_dot (tap j) (w j) x (htap j)

/-- `Layer.linear` at the stencil, and nothing else: `chan j` is which kernel
output `j` uses, which is the whole of what weight sharing is. -/
def Layer.conv (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → ℝ) (b : Vec ℝ m) : Layer S n m :=
  Layer.linear (tapMat tap fun j l => K (chan j) l) b

theorem Layer.conv_eval (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → ℝ) (b : Vec ℝ m) (htap : ∀ j, Function.Injective (tap j))
    (x : Vec ℝ n) (j : Fin m) :
    (Layer.conv (S := S) chan tap K b).eval x j = (∑ l, K (chan j) l * x (tap j l)) + b j := by
  show (tapMat tap (fun j l => K (chan j) l) *ᵥ x) j + b j = _
  rw [tapMat_mulVec _ _ htap]

end CORALean.Real
