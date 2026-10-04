import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.OutputEq.OutputEq
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.Recentre
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `LinearSys.canonicalFormFloat`

CORA's `canonicalForm` [1] at float zonotopes: `Ax + B u + c + E w → Ax + u'` with `u' ∈ U_ ⊕ u_`
and `Cx + D u + k + F v → Cx + v'` with `v' ∈ V_ ⊕ v_`. The centred zonotopes `U_`, `V_` are
zonotopes (`recentre` is exact), and the offsets `u_`, `v_`, which are real vectors of exact
sums at ℝ, are boxes here, each sum and product rounded outward. Soundness is
`canonicalFormFloat_state_outer` and `canonicalFormFloat_output_outer`.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m q r s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[linsys_, U_, u_, V_, v_] = canonicalForm(linsys, U, uVec, W, V, vVec)`, line by line, with
the offsets as boxes. -/
def LinearSys.canonicalFormFloat (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m) (c : Vec 𝕋 n)
    (out : OutputEq 𝕋 n m r) (k : Vec 𝕋 r) (E : Mat 𝕋 n q) (F : Mat 𝕋 r s)
    (U : Zonotope 𝕋 m) (uVec : Vec 𝕋 m) (W : Zonotope 𝕋 q) (V : Zonotope 𝕋 s)
    (vVec : Vec 𝕋 s) :
    LinearSys 𝕋 n × OutputEq 𝕋 n n r × Zonotope 𝕋 n × Interval (Vec 𝕋 n) × Zonotope 𝕋 r ×
      Interval (Vec 𝕋 r) :=
  let U₀ := U.recentre                                               -- U - centerU
  let W₀ := W.recentre                                               -- W - centerW
  let V₀ := V.recentre                                               -- V - centerV
  let v_ := ((Interval.mtimes out.D (Interval.point uVec)).plus (Interval.point k)).plus
    (Interval.mtimes F ((Interval.point V.c).plus (Interval.point vVec)))  -- offset on the output
  let V_ := (Zonotope.mtimes out.D (Zonotope.plus U₀ (Zonotope.point U.c))).plus
    (Zonotope.mtimes F V₀)                                           -- D (U + centerU) + F V
  let u_ := (((Interval.mtimes B (Interval.point uVec)).plus
    (Interval.mtimes B (Interval.point U.c))).plus (Interval.point c)).plus
    (Interval.mtimes E (Interval.point W.c))                         -- offset on the state
  let U_ := (Zonotope.mtimes B U₀).plus (Zonotope.mtimes E W₀)       -- B U + E W
  (⟨sys.A⟩, ⟨out.C, fun _ _ => zero⟩, U_, u_, V_, v_)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
