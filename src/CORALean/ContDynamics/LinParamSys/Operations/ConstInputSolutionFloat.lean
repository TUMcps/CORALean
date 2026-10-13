import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat

/-!
# What a constant input contributes over one step at every member, in floats

`LinParamSys.constInputSolution` computed in `𝕋`: the constant `ũ` is an admissible input
of the segment `[0, ũ]`, which holds the origin, so by [1, Thm. 3.1] and [1, Prop. 3.3] its
contribution at any time of `[0, r]` lies in `inputSolutionFloat` of that segment. No
correction matrix `F̃` is needed: the segment's own enclosure already holds the constant.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the constant `ũ` contributes at any time of `[0, r]`, at every member of
`sys.A`: `C(r)` applied to `[0, ũ]`, at Taylor order `η`. -/
def LinParamSys.constInputSolutionFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (r : 𝕋) (η : ℕ) (uc : Vec 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  let O : Zonotope (Vec 𝕋 n) := OfScalarPoint.ofVec (S := fun k => Zonotope (Vec 𝕋 k))  -- {0}
    (fun _ => (zero : 𝕋))
  let ũ : Zonotope (Vec 𝕋 n) := OfScalarPoint.ofVec (S := fun k => Zonotope (Vec 𝕋 k)) uc  -- {ũ}
  let seg := LinComb.linComb O ũ                                       -- [0, ũ]
  sys.inputSolutionFloat r η seg                                       -- C(r) applied to [0, ũ]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
