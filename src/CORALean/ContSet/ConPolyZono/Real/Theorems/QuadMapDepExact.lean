module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope

@[expose] public section

/-!
# `quadMapDep` is exact where every coefficient is dependent

The expansion is `PolyZonotope`'s, at a fixed factor vector: a point is one sum once the center is
generator zero, and the product of two monomials is the monomial of the added exponent columns.
The two lemmas it needs are public there, since a set equality would not do: the constraint has to
survive with the *same* factor vector on both sides. The witnesses are unchanged, so the
constraint they satisfy is, `quadMapDep` copying `A`, `b` and `R` across.

## Inputs
* `Q` – family of quadratic forms
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the image under the quadratic map is the result's set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n m : ℕ}

/-- The map of a sum, expanded over pairs: `bilin_point` at `quadBilin`, whose
point is the same sum with an empty center. -/
private theorem PolyZonotope.aux_quadEval_sum_ext (Q : Fin m → Mat ℝ n n)
    (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    quadEval Q (∑ l, extM pZ a l • extG pZ l)
      = ∑ l, monomial (quadMapE pZ) a l • quadMapG Q pZ l := by -- --- PROOF ---
  -- the ascription is `bilin_point`'s statement with `quadMapDep`'s fields unfolded
  have h : quadEval Q (pZ.c + ∑ i, monomial pZ.E a i • pZ.G i)
      = (0 : Vec ℝ m) + ∑ l, monomial (quadMapE pZ) a l • quadMapG Q pZ l :=
    (PolyZonotope.bilin_point (PolyZonotope.quadBilin Q) pZ pZ rfl a).symm
  rw [PolyZonotope.sum_ext_eq_point pZ a, h, zero_add]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMapDep_exact (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n))
    (hq : cPZ.qI = 0) : -- --- CONCL ---
    quadEval Q '' cPZ.construct = (cPZ.quadMapDep Q).construct := by -- --- PROOF ---
  have hz : ∀ b : Fin cPZ.qI → ℝ, ∑ j, b j • cPZ.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hquad : ∀ a : Fin cPZ.p → ℝ,
      quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i)
        = ∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l := by
    intro a
    have h := PolyZonotope.aux_quadEval_sum_ext Q cPZ.polyZonotope a
    rw [PolyZonotope.sum_ext_eq_point cPZ.polyZonotope a] at h
    exact h
  -- both directions are `hquad` at the same `a`, the independent block being empty
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, b, _, hsat, rfl⟩, rfl⟩
    refine ⟨a, fun _ => 0, fun j => j.elim0, hsat, ?_⟩
    show quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, b j • cPZ.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ k)
    rw [hz b, add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  -- back, with the independent coefficients read as zero
  · rintro _ ⟨a, b, _, hsat, rfl⟩
    refine ⟨cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, (0:ℝ) • cPZ.GI j,
      ⟨a, fun _ => 0, fun _ => by norm_num, hsat, rfl⟩, ?_⟩
    show quadEval Q (cPZ.c + ∑ i, monomial cPZ.E a i • cPZ.G i + ∑ j, (0:ℝ) • cPZ.GI j)
        = (0 : Vec ℝ k)
          + (∑ l, monomial (quadMapE cPZ.polyZonotope) a l • quadMapG Q cPZ.polyZonotope l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ k)
    rw [hz (fun _ => (0:ℝ)), add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
