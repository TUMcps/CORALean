module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInitFloat
public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombSameCenter
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominalErr
public import CORALean.ContSet.ConZonotope.Float.Operations.ZeroFeasible
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Zonotope.Float.Operations.PlusBox

@[expose] public section

/-!
# `Alg. 3` lines 7-12 in floats: one iteration of the main loop, from the inside

`maxBackReachStep` computed in `𝕋`, inside the exact layer's set (`maxBackReachStepFloat_encloses`).
What is subtracted rounds towards a larger set and what is kept towards a smaller one; the margin
is paid once, in line 10. Lines 8-10 are outer float sets with their excess recorded (`UErr`).
`aux_maxBackReachErosionFloat` is the distance the hull keeps from the exact eroded set for line
12's map, rounded, and for `Z̲_U`'s excess; `Ẑ_W(τ_k)` is widened by it, so line 11's erosion keeps
that distance. Line 11 is `maxBackReachCZFloat`, whose hull `linCombSameCenter` is exact since
both sets share the conversion box's center. `none` when an order search fails or the box's center
is not in a converted set (`ConZonotope.zeroFeasible`); the box `Bx` is the caller's.

## Inputs
* `sys` – linear system
* `Bx` – conversion box
* `P₁` – first eroded float polytope
* `P₂` – second eroded float polytope
* `U` – input float zonotope
* `W₀` – initial disturbance float zonotope
* `Zw` – center trajectory contribution over a bracket
* `Δt` – float step length
* `η` – Taylor order
* `s` – float loop state

## Output
* next float loop state from the inside, if the step succeeds

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The distance, per coordinate, the hull has to keep from the exact one's boundary: `Φn` and
`Ψ` bracket `e^{-A t_{k+1}}` and `e^{A t_{k+1}}`, the hull `H` is the set mapped, `ζ` bounds its
points and `DU` is the second summand's own distance after the map. -/
def LinearSys.aux_maxBackReachErosionFloat (Φn Ψ : Interval (Mat 𝕋 n n))
    (H : ConZonotope 𝕋 (Vec 𝕋 n)) (ζ DU : Vec 𝕋 n) : Vec 𝕋 n :=
  let W : Mat 𝕋 n n := fun i k => subUp (Φn.sup i k) (Φn.inf i k)   -- |Φ̄ - Φ|, entrywise
  let ε := ConZonotope.mtimesNominalErr Φn.inf H                    -- rounding of Φ̄ z
  let D : Vec 𝕋 n := fun i => addUp (dotUp (W i) ζ) (ε i)           -- |Φ̄ z - Φ z| plus rounding
  let DD : Vec 𝕋 n := fun i => addUp (D i) (DU i)                   -- with the second summand's
  fun i => dotUp (Ψ.magnitudeMat i) DD                              -- carried back by e^{At}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 7-12: one iteration of [1, Alg. 3]'s main loop from the inside. `Zw tLo tHi` holds
`Ẑ_W`'s disturbance part at every time of the bracket. -/
def LinearSys.maxBackReachStepFloat (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) (U W₀ : Zonotope (Vec 𝕋 n))
    (Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η : ℕ) (s : LinearSys.MaxBackReachStateFloat 𝕋 n) :
    Option (LinearSys.MaxBackReachStateFloat 𝕋 n) := do
  -- 7. t_{k+1} ← t_k + Δt
  let tk1Lo := addDown s.tEnc.inf Δt
  let tk1Hi := addUp s.tEnc.sup Δt
  let ηk ← sys.reachOrderFloat s.tEnc.inf s.tEnc.sup η             -- the orders, raised until
  let ηk1 ← sys.reachOrderFloat tk1Lo tk1Hi η                       -- admissible at each bracket
  let ηn ← sys.reachOrderFloat (neg tk1Hi) (neg tk1Lo) η
  let η' ← sys.reachOrderFloat Δt Δt η
  -- 7. [e^{A t_k}]
  let Φk := sys.expIntervalFloat s.tEnc.inf s.tEnc.sup ηk
  let Ψ := sys.expIntervalFloat tk1Lo tk1Hi ηk1                     -- [e^{A t_{k+1}}]
  let Φn := sys.expIntervalFloat (neg tk1Hi) (neg tk1Lo) ηn         -- [e^{-A t_{k+1}}]
  let I := MatExp.adaptiveIntegral (Interval.point sys.A) Δt η'     -- [∫₀^Δt e^{As}ds]
  let M := Interval.matMul Φk I                                     -- [e^{A t_k} ∫₀^Δt e^{As}ds]
  let T := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) M U
  -- 8. Z̲_U(t_{k+1})
  let ZU := s.ZU ⊞ T
  let UErr : Vec 𝕋 n := fun i =>                                    -- what ZU lies outside by
    addUp (addUp (s.UErr i) ((Zonotope.mtimesIntervalMatBox M U).magnitude i))
      ((Zonotope.plusBox s.ZU T).magnitude i)
  -- 9. Ẑ_{W₀}(t_{k+1})
  let ZW₀ := s.ZW₀ ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) Φk
    (sys.inputSolutionFloat Δt η' W₀)
  -- 10. Ẑ_W(τ_k)
  let ZW := ZW₀ ⊞ Zw s.tEnc.inf s.tEnc.sup
  let Z₀ := Bx.zonotope                                             -- the conversion box
  let ζ : Vec 𝕋 n := fun k =>                                       -- |z| for a point of the hull
    addUp (absolute (Z₀.c k)) (radius (fun i j => Z₀.G j i) k)
  let DU : Vec 𝕋 n := fun i =>                                      -- -Z̲_U(t_k) after the map
    addUp ((Zonotope.mtimesIntervalMatBox Φn s.ZU).magnitude i) (dotUp (Φn.magnitudeMat i) s.UErr)
  let Hs := (P₁.conZonotopeInner Bx).linCombSameCenter (P₂.conZonotopeInner Bx)  -- its shape
  let ρe := LinearSys.aux_maxBackReachErosionFloat Φn Ψ Hs ζ DU         -- the margin line 12 needs
  let ZWe := ZW ⊞ (Interval.mk (-ρe) ρe).zonotope  -- Ẑ_W(τ_k), widened by it
  -- 11. CZ(P₁ ⊖ Ẑ_W(τ_k))
  let C₁ := LinearSys.maxBackReachCZFloat Bx P₁ ZWe
  -- 11. CZ(P₂ ⊖ Ẑ_W(τ_k))
  let C₂ := LinearSys.maxBackReachCZFloat Bx P₂ ZWe
  -- 11. conv(CZ(…), CZ(…))
  let H := C₁.linCombSameCenter C₂
  if C₁.zeroFeasible && C₂.zeroFeasible then
    pure { tEnc := ⟨tk1Lo, tk1Hi⟩
           ZU := ZU
           UErr := UErr
           ZW₀ := ZW₀
           ZW := ZW
           -- 12. e^{-A t_{k+1}} CZ …
           RH := H.mtimesNominal Φn.inf
           RU := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- … Z̲_U
             (S := 𝒵[𝕋]) Φn s.ZU }
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
