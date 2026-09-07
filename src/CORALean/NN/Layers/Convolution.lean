import CORALean.NN.Layers.Linear

/-!
# The convolution layer

CORA's `nnConv2DLayer`, which is not a layer at all: a convolution is
`Layer.linear` at a particular matrix, by definition. `Layer.conv` contributes no
`enclose` of its own — only the matrix, and `conv_sound` naming the map it is.

A convolution's weights are shared and its matrix is sparse, and neither buys
anything here. Sharing is a property of the *argument*, `tapMat` taking a weight
per output and per tap; sparsity is a property of the arithmetic, so exploiting
it is an optimisation of `Mtimes` one layer below.

`tap j l` is the input coordinate that tap `l` of output `j` reads, which puts
padding, stride, dilation and the channel layout into one index function, all
that is asked of it being `Function.Injective (tap j)`.

`tapEntry` is a recursion rather than `∑ l, if tap j l = i then w j l else 0`: the
two agree — `tapEntry_dot` — but a sum of `k` terms rounds where picking the one
that matches does not, and the float layer needs the stored kernel exactly.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

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
      (∀ l, t l ≠ i) → tapEntry t v i = 0 := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro t v i h
    show (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i) = 0
    rw [if_neg (h 0)]
    exact ih _ _ _ fun l => h l.succ

/-- The row read against a vector is the weighted sum over the taps, which makes
`tapMat` the matrix of a stencil. Injectivity is what a window reading one input
twice would break: the matrix holds one weight per entry, the sum two. -/
theorem tapEntry_dot {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → ℝ) (x : Vec ℝ n),
      Function.Injective t → ∑ i, tapEntry t v i * x i = ∑ l, v l * x (t l) := by -- --- PROOF ---
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
    -- injectivity is what makes the first tap's entry vanish from the rest
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.conv_sound (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → ℝ) (b : Vec ℝ m) (htap : ∀ j, Function.Injective (tap j)) :
    (Layer.conv (S := S) chan tap K b).Sound
      fun x j => (∑ l, K (chan j) l * x (tap j l)) + b j :=
  (Layer.linear_sound _ b).congr fun x => funext fun j => by
    show (∑ l, K (chan j) l * x (tap j l)) + b j
      = (tapMat tap (fun j l => K (chan j) l) *ᵥ x) j + b j
    rw [tapMat_mulVec _ _ htap]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
