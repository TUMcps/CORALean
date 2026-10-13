import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
import CORALean.ContSet.Interval.Float.Operations.Magnitude
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse

/-!
# A float Newton test for a zero in a box

What turns a float Newton iterate `c` into a certificate. `G` and `J` are interval extensions of a
map `g : ℝᵏ → ℝᵏ` and of its slope; the test takes an approximate inverse `R` of the Jacobian at
`c` (`Zonotope.basisInverse` of the centre of `J` at the point `c`, trusted for nothing, and
stored, as `materialiseMat` does, so it is eliminated once rather than per entry read), the box
`B = c ± r`, and checks in outward rounding that every row of `|1 - R J(B)|` sums to some `qᵢ < 1`
and that `qᵢ r + |R g(c)|ᵢ ≤ r`: Krawczyk's operator over `B`, bounded by magnitudes, lies in `B`.
`true` certifies exactly one zero of `g` within `r` of `c` in the sup norm
(`NonlinDASys.newtonTestFloat_sound`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether the box `c ± r` passes the magnitude form of Krawczyk's test for the interval
extension `G` with slope enclosure `J`. -/
def NonlinDASys.newtonTestFloat (G : Interval (Vec 𝕋 k) → Interval (Vec 𝕋 k))
    (J : Interval (Vec 𝕋 k) → Interval (Mat 𝕋 k k)) (c : Vec 𝕋 k) (r : 𝕋) : Bool :=
  -- approximate inverse of the Jacobian at the centre
  let R : Mat 𝕋 k k :=
    (Interval.point (Zonotope.basisInverse (J (Interval.point c)).centreMat)).materialiseMat.inf
  -- the box `c ± r`, rounded outward
  let B : Interval (Vec 𝕋 k) := ⟨fun i => subDown (c i) r, fun i => addUp (c i) r⟩
  -- `R J(B)`, and the row sums of `|R J(B) - 1|`
  let E : Interval (Mat 𝕋 k k) := (Interval.matMul (Interval.point R) (J B)).materialiseMat
  let I : Mat 𝕋 k k := fun i j => if i = j then one else zero
  let q : Vec 𝕋 k := fun i => sumUp fun j => (Interval.matResidual E.inf E.sup I).magnitudeMat i j
  -- `|R g(c)|`
  let b : Vec 𝕋 k := (Interval.mtimes R (G (Interval.point c))).magnitude
  le zero r && (List.finRange k).all fun i =>
    ltStrict (q i) one && le (addUp (mulUp (q i) r) (b i)) r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
