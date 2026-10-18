module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.relax`

Each constraint row loosened from `(A μ_R(α))ᵢ = bᵢ` to `|(A μ_R(α))ᵢ - bᵢ| ≤ |sᵢ|`, still as a
constrained polynomial zonotope: row `i` gets one fresh factor `γᵢ`, which enters it alone, as the
monomial `γᵢ` with coefficient `sᵢ`, and enters no generator. `γᵢ ∈ [-1, 1]` is the slack.

Not one of CORA's operations: it is what a float set's per-row slack `b_error` denotes, so that the
float layer's nominal set is an exact `ConPolyZono` with `=` rows, and how an inequality row
becomes one (`ConZonotope.conPolyZono`). `mem_relax_iff` says what the result denotes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` widened by `|sᵢ|`: a fresh factor per row, read by that row alone. -/
def ConPolyZono.relax (cPZ : ConPolyZono α) (s : Vec ℝ cPZ.m) : ConPolyZono α where
  p := cPZ.p + cPZ.m
  h := cPZ.h
  qI := cPZ.qI
  m := cPZ.m
  q := cPZ.q + cPZ.m
  c := cPZ.c
  G := cPZ.G
  E := ConPolyZono.padE cPZ.E cPZ.m
  GI := cPZ.GI
  A := fun i => Fin.append (cPZ.A i) (Pi.single i (s i))
  b := cPZ.b
  R := PolyZonotope.plusE cPZ.R (PolyZonotope.identE cPZ.m)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
