import CORALean.ContDynamics.LinearSys.Operations.ReachErrorFloat
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRep

/-!
# The inner approximation of a sampled run, over a floating-point scalar

`reachInnerRep` computed in `𝕋`: the float sampled run, `discretizeEnclosureFloat`'s
`reach` with `inputSolutionFloat` as its input set, minus its budget
`reachErrorFloat`, by the float `Zonotope.minkDiffRep`. The real operation takes
`reachError` off the exact sampled run; this one takes off what the *float* run
owes against the exact held-input sampled set, which `reachErrorFloat` bounds
(`discretizeEnclosureFloat_reach_subset_add_errorFloat`).

`minkDiffRep` is inward-rounded and certified by a float containment check, at a
representation `M`, a margin factor `ρ` and a right inverse `H` the caller
offers. Any of them wrong gives `none`, costing precision and never soundness;
`reachInnerRepFloat_inner` is the guarantee on `some`. The result can also be a
point, where the budget has nearly outgrown the run.
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

/-- The float sampled run after `k` steps minus its budget, at the caller's representation `M`,
margin `ρ` and right inverse `H`: `none` where the certificate does not go through. -/
def LinearSys.reachInnerRepFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ)
    (M : Fin ((sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).h →
      Fin (sys.reachErrorFloat Δt η o ho R₀ U k).h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 ((sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let P := sys.inputSolutionFloat Δt η U                            -- the input set, in floats
  let R := (sys.discretizeEnclosureFloat Δt η).reach  -- R_k, the float run
    (S := fun k => Zonotope (Vec 𝕋 k))
    ⟨R₀, P, 0, k⟩ ⟨o, ho⟩
  let B := sys.reachErrorFloat Δt η o ho R₀ U k                     -- what it owes
  R.minkDiffRep B M ρ H                                             -- R ⊖ B, certified

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
