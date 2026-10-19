module

public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEqUnit

@[expose] public section

/-!
# The stored center is a point of the constrained polynomial zonotope

CORA's `center` returns the field `c` with no guarantee. Read as reals it is the nominal part's
point at the factors `0`, as in the exact layer's `center_mem_construct`: every monomial vanishes
when no exponent column of `E` or `R` is zero, so it is in the nominal set when `0` meets every
row within its slack, `|b| ≤ |b_error|`; it is then in the whole set once the error box holds
`0`, which a box built by the operations does and an arbitrary one need not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.center_mem_construct (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hE : Real.ConPolyZono.NoZeroCol cPZ.E) (hR : Real.ConPolyZono.NoZeroCol cPZ.cons.R)
    (hb : ∀ i, |toReal (cPZ.cons.b i)| ≤ |toReal (cPZ.cons.b_error i)|)
    (h0 : ∀ i, toReal (cPZ.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (cPZ.I_error.sup i)) : -- --- CONCL ---
    toRealVec cPZ.center ∈ cPZ.construct := by -- --- PROOF ---
  -- at the factors `0` every monomial vanishes, so the point is the center
  have hE0 : Real.PolyZonotope.monomial cPZ.E (fun _ => (0 : ℝ)) = 0 :=
    funext fun j => Real.ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl) j
  have hR0 : Real.PolyZonotope.monomial cPZ.cons.R (fun _ => (0 : ℝ)) = 0 :=
    funext fun j => Real.ConPolyZono.monomial_eq_zero_of_noZeroCol hR (fun _ => rfl) j
  have hN : toRealVec cPZ.center ∈ InflatedContSet.nominalSet cPZ := by
    refine ConPolyZono.mem_nominalSet_iff.mpr ⟨fun _ => 0, fun _ => 0, fun _ => by simp,
      fun _ => by simp, (PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).mpr
        ⟨fun _ => by simp, fun i => ?_⟩, fun i => ?_⟩
    · rw [hR0, Matrix.mulVec_zero, Pi.zero_apply, zero_sub, abs_neg]
      exact hb i
    · simp [hE0, ConPolyZono.center, toRealVec]
  exact ⟨_, hN, 0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
