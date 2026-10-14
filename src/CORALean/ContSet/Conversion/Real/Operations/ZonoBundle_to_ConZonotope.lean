module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.conZonotope (zB : ZonoBundle α) (i : Fin zB.k) : ConZonotope α :=
  (zB.zonotope i).conZonotope

/-- CORA's `conZonotope(zB)`: `cZ = conZonotope(zB.Z{1})`, then `cZ = and_(cZ, conZonotope(zB.Z{i}),
'exact')` for `i = 2, …, parallelSets`. -/
def ZonoBundle.conZonotopeAll (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ConZonotope (Vec ℝ n) :=
  let cZ₁ := (zB.Z ⟨0, hk⟩).conZonotope
  Fin.foldl (zB.k - 1)
    (fun cZ i =>
      let cZ_i := (zB.Z ⟨i + 1, by omega⟩).conZonotope
      cZ.intersection cZ_i)
    cZ₁

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
