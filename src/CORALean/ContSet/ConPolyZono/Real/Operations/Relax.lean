module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Relax

@[expose] public section

/-!
# `ConPolyZono.relax`

Each constraint row loosened from `(A μ_R(α))ᵢ = bᵢ` to `|(A μ_R(α))ᵢ - bᵢ| ≤ |sᵢ|`, still as a
constrained polynomial zonotope: the constraint is `PolyLevelSet.relax`, one fresh factor `γᵢ` per
row read by that row alone, and the fresh factors enter no generator. `γᵢ ∈ [-1, 1]` is the slack.

Not one of CORA's operations: it is what a float set's per-row slack `b_error` denotes, so that the
float layer's nominal set is an exact `ConPolyZono` with `=` rows, and how an inequality row
becomes one (`ConZonotope.conPolyZono`). `mem_relax_iff` says what the result denotes.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `s` – slack per constraint row

## Output
* same set with each row widened by its slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` widened by `|sᵢ|`: a fresh factor per row, read by that row alone. -/
def ConPolyZono.relax (cPZ : ConPolyZono α) (s : Vec ℝ cPZ.cons.m) : ConPolyZono α where
  p := cPZ.p + cPZ.cons.m
  h := cPZ.h
  qI := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := ConPolyZono.padE cPZ.E cPZ.cons.m
  GI := cPZ.GI
  cons := cPZ.cons.relax s (Interval.unit cPZ.cons.m)
  cons_eq := cPZ.cons_eq
  cons_dom := by
    show cPZ.cons.dom.append _ = _
    rw [cPZ.cons_dom, Interval.unit_append_unit]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
