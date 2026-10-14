module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.Recentre
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[linsys_, U_, u_, V_, v_] = canonicalForm(linsys, U, uVec, W, V, vVec)`, line by line, with
the offsets as boxes. -/
def LinearSys.canonicalFormFloat (sys : LinearSys 𝕋 n) (U : Zonotope (Vec 𝕋 sys.m))
    (uVec : Vec 𝕋 sys.m) (W : Zonotope (Vec 𝕋 sys.r)) (V : Zonotope (Vec 𝕋 sys.s))
    (vVec : Vec 𝕋 sys.s) :
    LinearSys 𝕋 n × Zonotope (Vec 𝕋 n) × Interval (Vec 𝕋 n) × Zonotope (Vec 𝕋 sys.q) ×
      Interval (Vec 𝕋 sys.q) :=
  let U₀ := U.recentre                                               -- U - centerU
  let W₀ := W.recentre                                               -- W - centerW
  let V₀ := V.recentre                                               -- V - centerV
  let v_ := ((Interval.mtimes sys.D (Interval.point uVec)).plus (Interval.point sys.k)).plus
    (Interval.mtimes sys.F ((Interval.point V.c).plus (Interval.point vVec)))  -- output offset
  let V_ := (Zonotope.mtimes sys.D (Zonotope.plus U₀ (Zonotope.point U.c))).plus
    (Zonotope.mtimes sys.F V₀)                                       -- D (U + centerU) + F V
  let u_ := (((Interval.mtimes sys.B (Interval.point uVec)).plus
    (Interval.mtimes sys.B (Interval.point U.c))).plus (Interval.point sys.c)).plus
    (Interval.mtimes sys.E (Interval.point W.c))                     -- offset on the state
  let U_ := (Zonotope.mtimes sys.B U₀).plus (Zonotope.mtimes sys.E W₀)  -- B U + E W
  let I : ∀ d, Mat 𝕋 d d := fun _ i j => if i = j then one else zero
  let sys_ : LinearSys 𝕋 n :=                                        -- A, I, 0, C, 0, 0, 0, I
    ⟨n, sys.q, n, sys.q, sys.A, I n, fun _ => zero, sys.C, fun _ _ => zero, fun _ => zero,
      fun _ _ => zero, I sys.q⟩
  (sys_, U_, u_, V_, v_)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
