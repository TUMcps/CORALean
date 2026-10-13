import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.NN.Layers.Operations.StarSetFloatContSet

/-!
# The chord row of a float star set

The third relaxation row of a ReLU neuron, `-k G_j α + β ≤ k (c_j - l)` with `k = u/(u-l)`,
over the factors with the new one `β` appended. `k` is only known within `[klo, khi]`, the
quotient rounded both ways, so the generator coefficients are `-(k G_jk)` rounded to the side
that makes the row weaker at the least `α`, and what that costs at the widest `α` of the box
is added to the right-hand side, together with `k (c_j - l)` rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The chord row for neuron `j` with bounds `b = (l, u)`. -/
def StarSet.chordRow (s : StarSet 𝕋 n) (j : Fin n) (b : 𝕋 × 𝕋) :
    (Fin (s.m + 1) → 𝕋) × 𝕋 :=
  let klo := divDown b.2 (subUp b.2 b.1)
  let khi := divUp b.2 (subDown b.2 b.1)
  (Fin.snoc (α := fun _ => 𝕋)
      (fun k => neg (Interval.mulLo klo khi (s.G j k) (s.G j k))) one,
   addUp (Interval.mulHi klo khi (subDown (s.c j) b.1) (subUp (s.c j) b.1))
     (sumUp fun k => mulUp
       (subUp (Interval.mulHi klo khi (s.G j k) (s.G j k))
         (Interval.mulLo klo khi (s.G j k) (s.G j k)))
       (maximum (absolute (s.l k)) (absolute (s.u k)))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
