module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxVecIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEqUnit

@[expose] public section

/-!
# Membership in the nominal constrained polynomial zonotope

The form every enclosure proof at this layer reads the nominal half of a point
in: the center and the two generator blocks through `toReal`, the exponent
matrices unrounded, and the constraint as membership in this set's own `cons`: the slack factors
of `Real.ConPolyZono.relax` are read away into each row's `|b_error|` (`mem_relax_vec_iff`).

Proofs use it rather than going through `nominal` because through it every count
is `cPZ.h`, where the instance gives the equal-but-distinct `(nominal cPZ).h` that
`rw` reads apart.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    {x : Vec ℝ n} : -- --- STMT ---
    x ∈ InflatedContSet.nominalSet cPZ ↔ ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ,
      (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1) ∧ a ∈ cPZ.cons.construct ∧ ∀ i, x i = toReal (cPZ.c i)
        + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E a l)
        + ∑ j, toReal (cPZ.GI j i) * β j :=
  (Real.ConPolyZono.mem_relax_vec_iff _ _).trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun ha => and_congr Iff.rfl <| and_congr
      ((PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).trans
        (and_iff_right ha)).symm Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
