module

public import CORALean.ContSet.Taylm.Float.Operations.OptBernstein
public import CORALean.ContSet.Taylm.Float.Theorems.BernsteinCoeffBoundsMem
public import CORALean.ContSet.Taylm.Float.Theorems.MemBernsteinIdx
public import CORALean.ContSet.Taylm.Float.Theorems.ListMinLe
public import CORALean.ContSet.Taylm.Float.Theorems.LeListMax
public import CORALean.ContSet.Taylm.Real.Theorems.OptBernsteinMem

@[expose] public section

/-!
# `optBernstein` encloses, over a floating-point scalar

On the box, a function the float model encloses lies between the two floats `optBernstein`
returns: each float coefficient bracket contains the exact coefficient of the model the floats
read as, so the least lower end is at most the exact least coefficient, the greatest upper end at
least the exact greatest, and the exact `Taylm.optBernstein_mem` does the rest. Not exact, as the
exact bound is not.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the Bernstein enclosure contains the function's value
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBernstein_mem (T : Taylm 𝕋 n) {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) :
    toReal (Taylm.optBernstein T).inf ≤ f t ∧ f t ≤ toReal (Taylm.optBernstein T).sup
    := by -- --- PROOF ---
  -- the exact bound, and the exact degree the float degree reads as
  have hr := Real.Taylm.optBernstein_mem h ht
  have hN : T.nominal.bernsteinDegree
      = (T.terms.map fun a => Finset.univ.sup a.2).foldr max 0 := by
    simp [Real.Taylm.bernsteinDegree, Taylm.nominal, List.map_map, Function.comp_def]
  unfold Taylm.optBernstein
  -- fix the degree, then bracket the least and the greatest coefficient
  generalize (T.terms.map fun a => Finset.univ.sup a.2).foldr max 0 = N at hN ⊢
  subst hN
  simp only [Real.Taylm.optBernstein] at hr
  -- every coefficient bracket lies below, respectively above, the exact extreme
  have hlo : toReal (Taylm.listMin (fun β => (Taylm.bernsteinCoeffBounds T.terms
        T.nominal.bernsteinDegree β).inf) (Taylm.bernsteinIdx n T.nominal.bernsteinDegree))
      ≤ Finset.univ.inf' ⟨fun _ => 0, Finset.mem_univ _⟩
        (Real.Taylm.bernsteinCoeff T.nominal.terms T.nominal.bernsteinDegree) :=
    Finset.le_inf' _ _ fun β _ => le_trans
      (Taylm.listMin_le _ (Taylm.mem_bernsteinIdx n _ β))
      (Taylm.bernsteinCoeffBounds_mem T.terms _ β).1
  -- and the greatest above
  have hhi : Finset.univ.sup' ⟨fun _ => 0, Finset.mem_univ _⟩
        (Real.Taylm.bernsteinCoeff T.nominal.terms T.nominal.bernsteinDegree)
      ≤ toReal (Taylm.listMax (fun β => (Taylm.bernsteinCoeffBounds T.terms
        T.nominal.bernsteinDegree β).sup) (Taylm.bernsteinIdx n T.nominal.bernsteinDegree)) :=
    Finset.sup'_le _ _ fun β _ => le_trans
      (Taylm.bernsteinCoeffBounds_mem T.terms _ β).2
      (Taylm.le_listMax (fun β => (Taylm.bernsteinCoeffBounds T.terms
        T.nominal.bernsteinDegree β).sup) (Taylm.mem_bernsteinIdx n _ β))
  constructor
  · refine le_trans (addDown_le_add _ _) (le_trans ?_ hr.1)
    exact add_le_add hlo (addDown_le_add _ _)
  · refine le_trans hr.2 (le_trans ?_ (add_le_addUp _ _))
    exact add_le_add hhi (add_le_addUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
