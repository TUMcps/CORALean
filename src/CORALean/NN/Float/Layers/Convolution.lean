import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Layers.Convolution

/-!
# The convolution layer over a floating-point scalar

`Float.Layer.linear` at the same stencil matrix, and it rounds nowhere — which
is the point of building the matrix by `tapEntry` rather than by a sum.

An entry of a stencil matrix is one kernel weight or zero. Written as
`∑ l, if tap j l = i then w j l else 0` that is `k` floating-point additions
whichever way they are rounded, and the matrix read back into ℝ would then be
the convolution only approximately; written as a recursion that stops at the
first tap reading `i`, it is a *placement*, no `FloatOps` operation is consulted
at all, and `toRealMat_tapMat` is an equality with no hypothesis.

So the float convolution encloses exactly the convolution the stored kernel
denotes, and everything after it — the multiplication by the set, the bias —
rounds inside `mtimes` and `plus` as the linear layer's does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋] {n m k c : ℕ}

/-- The exact layer's recursion with the scalar swapped, and `zero` where it has
`0`: no arithmetic, so nothing rounds. -/
def tapEntry {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Fin k → 𝕋) → Fin n → 𝕋
  | 0, _, _, _ => zero
  | _ + 1, t, v, i =>
    if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i

theorem toReal_tapEntry {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (i : Fin n),
      toReal (tapEntry t v i) = Real.tapEntry t (fun l => toReal (v l)) i := by
  intro k
  induction k with
  | zero => intro _ _ _; exact toReal_zero
  | succ k ih =>
    intro t v i
    show toReal (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i)
      = (if t 0 = i then toReal (v 0)
        else Real.tapEntry (fun l => t l.succ) (fun l => toReal (v l.succ)) i)
    by_cases hi : t 0 = i
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      exact ih _ _ _

def tapMat (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋) : Mat 𝕋 m n :=
  fun j i => tapEntry (tap j) (w j) i

/-- An equality with no hypothesis: the float matrix denotes the exact layer's
matrix at the weights that were read in. -/
theorem toRealMat_tapMat (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋) :
    toRealMat (tapMat tap w) = Real.tapMat tap fun j l => toReal (w j l) := by
  funext j i
  exact toReal_tapEntry (tap j) (w j) i

def Layer.conv (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) : Real.Layer S n m :=
  Layer.linear (tapMat tap fun j l => K (chan j) l) b

theorem Layer.conv_eval (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) (htap : ∀ j, Function.Injective (tap j))
    (x : Vec ℝ n) (j : Fin m) :
    (Layer.conv (S := S) chan tap K b).eval x j
      = (∑ l, toReal (K (chan j) l) * x (tap j l)) + toReal (b j) := by
  show (toRealMat (tapMat tap fun j l => K (chan j) l) *ᵥ x) j + toRealVec b j = _
  rw [toRealMat_tapMat, Real.tapMat_mulVec _ _ htap]
  rfl

end CORALean.Float
