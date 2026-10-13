import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane
import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# CORA's `projectOnHyperplane`, at an interval normal and offset

`(I − c cᵀ) S + δ c` for the hyperplane `{x | cᵀx = δ}` with `c` known only to lie in the box
`[c̲, c̄]` and `δ` in `[δ̲, δ̄]`: what a normalized normal `n/‖n‖` is, once the norm is a
directed square root. `projectOnHyperplaneFloat` takes one rounded normal, and so projects onto
a hyperplane near the one meant; here each entry `δᵢⱼ − cᵢcⱼ` of the projector is bracketed by
the corner products of the two boxes, and `δ c` likewise, so the result holds the projection
of every point onto every hyperplane the boxes allow, the meant one among them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (fun m n => Interval (Mat 𝕋 m n)) S]
variable [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def ContSet.projectOnHyperplaneIntervalFloat (s : S n) (c : Interval (Vec 𝕋 n)) (dLo dHi : 𝕋) :
    S n :=
  -- the projector `I − c cᵀ`, each entry bracketed over the box of `c`
  let A : Interval (Mat 𝕋 n n) :=
    ⟨fun i j => subDown (if i = j then one else zero)
        (Interval.mulHi (c.inf i) (c.sup i) (c.inf j) (c.sup j)),
      fun i j => subUp (if i = j then one else zero)
        (Interval.mulLo (c.inf i) (c.sup i) (c.inf j) (c.sup j))⟩
  -- the translation `δ c`, bracketed over both boxes
  let b : Interval (Vec 𝕋 n) :=
    ⟨fun i => Interval.mulLo dLo dHi (c.inf i) (c.sup i),
      fun i => Interval.mulHi dLo dHi (c.inf i) (c.sup i)⟩
  Plus.plus (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) A s) (OfInterval.ofInterval b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
