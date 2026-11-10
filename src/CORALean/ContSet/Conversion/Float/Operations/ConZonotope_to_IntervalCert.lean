module

public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalTight
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# A constrained zonotope as a box from dual certificates, over a floating-point scalar

CORA's `conZonotope/interval` solves `max / min eᵢᵀ(c + Gβ)` over `Aβ = b`, `|β| ≤ 1`, per
coordinate. Weak duality bounds each program from any multiplier by a value that is checked, not
trusted: `ConZonotope.boundDotWeights`, in directed rounding, the residual `‖Gᵢ − Aᵀy‖₁` paid by
the unit box. A bound along `eᵢ` is the upper end of coordinate `i`, one along `−eᵢ` the negated
lower end. A poor multiplier loosens the box and never makes it unsound; all zero is the
zonotope's box. `intervalCertWith` takes the multipliers of each end, as an LP solver outside Lean
computes them; `intervalCert` proposes them itself, by the exact simplex at ℚ
(`HPolytope.dualWeights`).

## Inputs
* `cZ` – float constrained zonotope
* `up` – multipliers of the upper end of each coordinate
* `lo` – multipliers of the lower end of each coordinate

## Output
* box holding the set, tight where the multipliers are near an optimal dual solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The multipliers of one bound: for the inequality rows, and for the upper and lower halves of the
equality rows. -/
abbrev ConZonotope.CertWeights (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Type :=
  Vec 𝕋 cZ.P.m × Vec 𝕋 cZ.P.me × Vec 𝕋 cZ.P.me

/-- The direction `s · eᵢ`, `s` being `one` or `neg one`. -/
@[step_of ConZonotope.intervalCertWith]
def ConZonotope.step_axis (s : 𝕋) (i : Fin n) : Vec 𝕋 n := fun j => if j = i then s else zero

/-- The weak-duality bound along `a` at the multipliers `w`, `boundDotWeights` of the direction. -/
@[step_of ConZonotope.intervalCertWith]
def ConZonotope.step_certBound (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n)
    (w : ConZonotope.CertWeights cZ) : FloatBound 𝕋 cZ.toSet
      (Real.HPolytope.rowLin (toRealMat fun (_ : Fin 1) => a) 0) :=
  cZ.boundDotWeights a (fun _ => rfl) w.1 w.2.1 w.2.2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box whose upper end `i` bounds `eᵢᵀx` and whose lower end `i` is the negated bound of
`−eᵢᵀx`, each at the given multipliers. -/
def ConZonotope.intervalCertWith (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (up lo : Fin n → ConZonotope.CertWeights cZ) : Interval (Vec 𝕋 n) where
  inf := fun i => neg (ConZonotope.step_certBound cZ (ConZonotope.step_axis (neg one) i) (lo i)).val
  sup := fun i => (ConZonotope.step_certBound cZ (ConZonotope.step_axis one i) (up i)).val

/-- The multipliers the exact simplex at ℚ proposes for the direction `a`. -/
def ConZonotope.certCandidate [ToRat 𝕋] (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) :
    ConZonotope.CertWeights cZ :=
  cZ.P.dualWeights fun j => ∑ i, ToRat.toRat (a i) * ToRat.toRat (cZ.G j i)

/-- The multipliers the simplex proposes for the upper end of coordinate `i`. -/
def ConZonotope.certUp [ToRat 𝕋] (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin n) :
    ConZonotope.CertWeights cZ :=
  cZ.certCandidate (ConZonotope.step_axis one i)

/-- The multipliers the simplex proposes for the lower end of coordinate `i`. -/
def ConZonotope.certLo [ToRat 𝕋] (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin n) :
    ConZonotope.CertWeights cZ :=
  cZ.certCandidate (ConZonotope.step_axis (neg one) i)

/-- `intervalCertWith` at the multipliers the simplex proposes: a program per end. -/
def ConZonotope.intervalCert [ToRat 𝕋] (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  cZ.intervalCertWith cZ.certUp cZ.certLo

/-- The cut of the certificate box and the box of `k` Fourier-Motzkin passes, each outer. -/
def ConZonotope.intervalCertTight [ToRat 𝕋] (k : ℕ) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Interval (Vec 𝕋 n) :=
  (cZ.intervalCert).intersection (cZ.intervalTight k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
