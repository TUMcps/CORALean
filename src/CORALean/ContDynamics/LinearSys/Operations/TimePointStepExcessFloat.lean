module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionBoxFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInputFloat

@[expose] public section

/-!
# How far a float step reaches beyond the exact one

`timePointStepInputFloat` encloses the exact step from outside. This box bounds
the other side: the float step lies in `e^{Ar} X` plus the held-input
contribution `(∫₀^r e^{As} ds) U`, widened by this box and by the step's error
box `timePointStepErrorBoxFloat`
(`timePointStepInputFloat_subset_add_excess`). It holds what floats add:

* `mtimesIntervalMatBox`, the product `[e^{Ar}] X` beyond `e^{Ar} X` for the true
  exponential, a member of `[e^{Ar}]`;
* the `plusBox` of the float sum;
* `inputSolutionBoxFloat`, the input solution beyond the exact one.

The error box is kept apart because a run carries it separately, as
`reachInputErrorFloat` does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `timePointStepInputFloat r η X U` holds beyond the exact step, besides its error box:
the product's box, the sum's `plusBox` and the input solution's box. -/
def LinearSys.timePointStepExcessFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X U : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let eAr := sys.expIntervalFloat r r η                                     -- [e^{Ar}]
  let M := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- [e^{Ar}] X
    (S := fun k => Zonotope (Vec 𝕋 k)) eAr X
  let P := sys.inputSolutionFloat r η U                                     -- P(r), in floats
  ((Zonotope.mtimesIntervalMatBox eAr X).zonotope ⊞                         -- M beyond e^{Ar} X
    (Zonotope.plusBox M P).zonotope) ⊞                                      -- M ⊞ P beyond M + P
      sys.inputSolutionBoxFloat r η U                                       -- P beyond P exact

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
