module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachErosionFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInitFloat
public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombSameCentre
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.ZeroFeasible
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Zonotope.Float.Operations.PlusBox

@[expose] public section

/-!
# `Alg. 2` lines 7-12 in floats: one iteration of the main loop, from the inside

`maxBackReachStep` computed in `𝕋`, inside the exact layer's set (`maxBackReachStepFloat_encloses`).
What is subtracted rounds towards a larger set and what is kept towards a smaller one; the
margin between them is paid once, in line 10. Lines 8-10 are outer float sets with their excess
recorded (`UErr`). `maxBackReachErosionFloat` is the distance the hull keeps from the exact eroded
set for line 12's map at an interval matrix, rounded, and for `Z̲_U`'s excess; `Ẑ_W(τ_k)` is
widened by it, so line 11's erosion keeps that distance. Line 11 is `maxBackReachCZFloat`, whose
hull `linCombSameCentre` is exact since both sets share the conversion box's centre. Line 12's
first summand is the hull's stored numbers mapped by the lower matrix of `[e^{-A t_{k+1}}]`
(`mtimesNominal`), the second `[e^{-A t_{k+1}}] Z̲_U(t_k)` outer; the state keeps them apart.

`none` when an order search fails or the box's centre is not in a converted set
(`ConZonotope.zeroFeasible`, which the hull needs). The box `Bx` is the caller's and decides only
how much of each set the conversion covers.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 7-12: one iteration of [1, Alg. 2]'s main loop from the inside. `Zw tLo tHi` holds
`Ẑ_W`'s disturbance part at every time of the bracket. -/
def LinearSys.maxBackReachStepFloat (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) (U W₀ : Zonotope (Vec 𝕋 n))
    (Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η : ℕ) (s : LinearSys.MaxBackReachStateFloat 𝕋 n) :
    Option (LinearSys.MaxBackReachStateFloat 𝕋 n) := do
  let tk1Lo := addDown s.tLo Δt                                     -- 7. t_{k+1} ← t_k + Δt
  let tk1Hi := addUp s.tHi Δt
  let ηk ← sys.reachOrderFloat s.tLo s.tHi η                        -- the orders, raised until
  let ηk1 ← sys.reachOrderFloat tk1Lo tk1Hi η                       -- admissible at each bracket
  let ηn ← sys.reachOrderFloat (neg tk1Hi) (neg tk1Lo) η
  let η' ← sys.reachOrderFloat Δt Δt η
  let Φk := sys.expIntervalFloat s.tLo s.tHi ηk                     -- 7. [e^{A t_k}]
  let Ψ := sys.expIntervalFloat tk1Lo tk1Hi ηk1                     -- [e^{A t_{k+1}}]
  let Φn := sys.expIntervalFloat (neg tk1Hi) (neg tk1Lo) ηn         -- [e^{-A t_{k+1}}]
  let I := MatExp.adaptiveIntegral (Interval.point sys.A) Δt η'     -- [∫₀^Δt e^{As}ds]
  let M := Interval.matMul Φk I                                     -- [e^{A t_k} ∫₀^Δt e^{As}ds]
  let T := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) M U
  let ZU := s.ZU ⊞ T                                                -- 8. Z̲_U(t_{k+1})
  let UErr : Vec 𝕋 n := fun i =>                                    -- what ZU lies outside by
    addUp (addUp (s.UErr i) ((Zonotope.mtimesIntervalMatBox M U).magnitude i))
      ((Zonotope.plusBox s.ZU T).magnitude i)
  let ZW₀ := s.ZW₀ ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- 9. Ẑ_{W₀}(t_{k+1})
    (S := 𝒵[𝕋]) Φk
    (sys.inputSolutionFloat Δt η' W₀)
  let ZW := ZW₀ ⊞ Zw s.tLo s.tHi                                    -- 10. Ẑ_W(τ_k)
  let Z₀ := Bx.zonotope                                             -- the conversion box
  let ζ : Vec 𝕋 n := fun k =>                                       -- |z| for a point of the hull
    addUp (absolute (Z₀.c k)) (radius (fun i j => Z₀.G j i) k)
  let DU : Vec 𝕋 n := fun i =>                                      -- -Z̲_U(t_k) after the map
    addUp ((Zonotope.mtimesIntervalMatBox Φn s.ZU).magnitude i) (dotUp (Φn.magnitudeMat i) s.UErr)
  let Hs := (P₁.conZonotopeInner Bx).linCombSameCentre (P₂.conZonotopeInner Bx)  -- its shape
  let ρe := LinearSys.maxBackReachErosionFloat Φn Ψ Hs ζ DU         -- the margin line 12 needs
  let ZWe := ZW ⊞ (Interval.mk (fun i => neg (ρe i)) ρe).zonotope  -- Ẑ_W(τ_k), widened by it
  let C₁ := LinearSys.maxBackReachCZFloat Bx P₁ ZWe                 -- 11. CZ(P₁ ⊖ Ẑ_W(τ_k))
  let C₂ := LinearSys.maxBackReachCZFloat Bx P₂ ZWe                 -- 11. CZ(P₂ ⊖ Ẑ_W(τ_k))
  let H := C₁.linCombSameCentre C₂                                  -- 11. conv(CZ(…), CZ(…))
  if C₁.zeroFeasible && C₂.zeroFeasible then
    pure { tLo := tk1Lo
           tHi := tk1Hi
           ZU := ZU
           UErr := UErr
           ZW₀ := ZW₀
           ZW := ZW
           RH := H.mtimesNominal Φn.inf                             -- 12. e^{-A t_{k+1}} CZ …
           RU := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- … Z̲_U
             (S := 𝒵[𝕋]) Φn s.ZU }
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
