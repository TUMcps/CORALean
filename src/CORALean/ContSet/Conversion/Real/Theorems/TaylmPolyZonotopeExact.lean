module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmDepApply
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmIndepApply
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmPolyZonotopeContains

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope

CORA's `polyZonotope(taylm)`: the variables are the dependent factors, every term of every
coordinate a generator along that coordinate with the term's exponents, and each remainder
an independent generator about its centre. CORA also folds the constant terms into the
centre; here they stay generators at the zero exponent, the same set. Exact when every
remainder is a nonempty interval (`polyZonotope_exact`); the range set is always contained
(`polyZonotope_contains`), a point of it having a remainder value in each interval.

This is [1, Prop. 4] and, with `PolyZonotope.taylm_exact`, the equivalence of polynomial zonotopes
and Taylor models of [1, Fig. 1 (Polynomial Zonotopes ↔ Taylor Models)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyZonotope_exact (T : Fin m → Taylm n) (hT : ∀ i, (T i).rem.inf ≤ (T i).rem.sup) :
    (Taylm.polyZonotope T).construct = Taylm.construct T := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ (Taylm.polyZonotope_contains T)
  rintro x ⟨a, β, ha, hβ, rfl⟩
  refine ⟨a, ha, fun i => ?_⟩
  rw [Pi.add_apply, Pi.add_apply, Taylm.dep_apply, Taylm.indep_apply]
  simp only [Taylm.polyZonotope]
  have hr : 0 ≤ ((T i).rem.sup - (T i).rem.inf) / 2 := by linarith [hT i]
  have hb := abs_le.1 (hβ i)
  constructor <;> nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
