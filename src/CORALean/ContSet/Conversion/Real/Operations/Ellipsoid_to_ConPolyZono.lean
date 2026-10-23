module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope

## Inputs
* `k` – number of factors

## Output
* diagonal constraint exponent matrix with a slack row
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The diagonal constraint exponent matrix: factor `j` reads its own square
everywhere except the last row, which reads the slack factor to the first
power alone. -/
def Ellipsoid.conPolyZonoR (k : ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun r c => if r = c then (if c.val < k then 2 else 1) else 0

/-- CORA's construction for any factor `G` of the shape matrix (`G Gᵀ = Q`; CORA takes `V √D` from
`Q`'s eigendecomposition): `n` dependent factors read `G`'s columns exactly as `G *ᵥ u` does, and
one further factor absorbs the unit ball's radius slack. -/
noncomputable def Ellipsoid.conPolyZonoOfFactor (G : Mat ℝ n n) (q : Vec ℝ n) :
    ConPolyZono (Vec ℝ n) where
  p := n + 1
  h := n
  qI := 0
  c := q
  G := ConPolyZono.consCol G
  E := ConPolyZono.padE (PolyZonotope.identE n) 1
  GI := Fin.elim0
  cons := ⟨1, n + 1, fun _ j => if j.val < n then 1 else -(1 / 2), Ellipsoid.conPolyZonoR n,
    fun _ => (1 / 2 : ℝ), fun _ => .eq, Interval.unit (n + 1)⟩
  cons_eq _ := rfl
  cons_dom := rfl

/-- The conversion with the factor `G = Q^(1/2)`. -/
noncomputable def Ellipsoid.conPolyZono (E : Ellipsoid n) : ConPolyZono (Vec ℝ n) :=
  Ellipsoid.conPolyZonoOfFactor E.G E.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
