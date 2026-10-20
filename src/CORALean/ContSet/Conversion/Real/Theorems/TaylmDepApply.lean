module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope: `dep_apply`

## Inputs
* `T` – Taylor models, one per coordinate
* `a` – evaluation point
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* dependent part evaluates to the model polynomial
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.dep_apply (T : Fin m → Taylm n) (a : Vec ℝ n) (i : Fin m) : -- --- CONCL ---
    (∑ j, PolyZonotope.monomial (Taylm.polyZonotope T).E a j • (Taylm.polyZonotope T).G j) i
      = (T i).poly a := by -- --- PROOF ---
  rw [Finset.sum_apply]
  have hg : ∀ j : Fin (Taylm.polyZonotope T).h,
      (PolyZonotope.monomial (Taylm.polyZonotope T).E a j • (Taylm.polyZonotope T).G j) i
        = (fun x : Fin m × (ℝ × (Fin n → ℕ)) =>
            if x.1 = i then x.2.1 * Taylm.monomial x.2.2 a else 0)
          ((Taylm.allTerms T).get j) := by
    intro j
    -- the generator is nonzero only along its own coordinate
    simp only [Taylm.polyZonotope, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h1 h2 h2
    · simp [PolyZonotope.monomial, Taylm.monomial, mul_comm]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  -- a sum over the generator indices is a sum over the term list
  rw [Finset.sum_congr rfl fun j _ => hg j]
  have key : ∀ (L : List (Fin m × (ℝ × (Fin n → ℕ)))) (g : Fin m × (ℝ × (Fin n → ℕ)) → ℝ),
      ∑ j : Fin L.length, g (L.get j) = (L.map g).sum := by
    intro L g
    rw [← List.sum_ofFn]
    congr 1
    exact List.ext_get (by simp) fun k h1 h2 => by simp
  show ∑ j : Fin (Taylm.allTerms T).length, _ = _
  refine Eq.trans (key (Taylm.allTerms T)
    (fun x => if x.1 = i then x.2.1 * Taylm.monomial x.2.2 a else 0)) ?_
  simp only [Taylm.allTerms, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  -- coordinate `i` collects exactly the terms of model `i`
  have hrow : ∀ i' : Fin m, (List.sum ∘
      (List.map fun x : Fin m × (ℝ × (Fin n → ℕ)) =>
        if x.1 = i then x.2.1 * Taylm.monomial x.2.2 a else 0) ∘ fun i' =>
          List.map (fun b => (i', b)) (T i').terms) i'
      = if i' = i then (T i).poly a else 0 := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp [Taylm.poly, Taylm.polyOf, Function.comp_def]
    · simp [h, Function.comp_def]
  rw [List.map_congr_left fun i' _ => hrow i', ← List.ofFn_eq_map, List.sum_ofFn]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
