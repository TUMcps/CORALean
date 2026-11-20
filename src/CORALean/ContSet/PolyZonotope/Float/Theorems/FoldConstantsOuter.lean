module

public import CORALean.ContSet.PolyZonotope.Float.Operations.FoldConstants
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `PolyZonotope.foldConstants` encloses the set

A generator without a factor has the monomial one, so it moves into the center; the sums stored
rounded up are off by at most the widths added up beside them, which the error box takes.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is contained in the folded set
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum splits into the elements that satisfy a test and the others. -/
private theorem PolyZonotope.aux_sum_filter {α : Type} (L : List α) (p : α → Bool) (f : α → ℝ) :
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter fun x => !p x).map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases hp : p x <;> simp [hp, ih] <;> ring

/-- The sums stored rounded up are off by at most the widths added up beside them. -/
private theorem PolyZonotope.aux_fold {h : ℕ} (g : Fin h → 𝕋) (F : 𝕋 × 𝕋 → Fin h → 𝕋 × 𝕋)
    (hF : ∀ acc l, F acc l = (addUp acc.1 (g l),
      addUp acc.2 (subUp (addUp acc.1 (g l)) (addDown acc.1 (g l)))))
    (K : List (Fin h)) (acc : 𝕋 × 𝕋) : -- --- CONCL ---
    |toReal acc.1 + (K.map fun l => toReal (g l)).sum - toReal (K.foldl F acc).1| + toReal acc.2
      ≤ toReal (K.foldl F acc).2 := by -- --- PROOF ---
  induction K generalizing acc with
  | nil => simp
  | cons l K ih =>
    have hi := ih (F acc l)
    rw [hF] at hi
    rw [List.foldl_cons, hF]
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    -- the rounding of this sum, and the rest by the hypothesis
    have h₁ := add_le_addUp acc.1 (g l)
    have h₂ := addDown_le_add acc.1 (g l)
    have h₃ := add_le_addUp (addUp acc.1 (g l)) (neg (addDown acc.1 (g l)))
    have h₄ := add_le_addUp acc.2 (subUp (addUp acc.1 (g l)) (addDown acc.1 (g l)))
    rw [toReal_neg] at h₃
    simp only [subUp] at h₄ hi ⊢
    set R := toReal (K.foldl F (addUp acc.1 (g l),
      addUp acc.2 (addUp (addUp acc.1 (g l)) (neg (addDown acc.1 (g l)))))).1
    set u := toReal (addUp acc.1 (g l))
    set Sr := (K.map fun l => toReal (g l)).sum
    have htri := abs_add_le (toReal acc.1 + toReal (g l) - u) (u + Sr - R)
    have e : toReal acc.1 + toReal (g l) - u + (u + Sr - R)
        = toReal acc.1 + (toReal (g l) + Sr) - R := by ring
    rw [e] at htri
    have hw : |toReal acc.1 + toReal (g l) - u| ≤ u - toReal (addDown acc.1 (g l)) := by
      rw [abs_le]; constructor <;> linarith
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.foldConstants_outer (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    pZ.toSet ⊆ pZ.foldConstants.toSet := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  -- the names of the definition
  set isConst : Fin pZ.h → Bool := fun l => (List.finRange pZ.p).all fun k => pZ.E k l == 0
  set K := (List.finRange pZ.h).filter isConst
  set keep : Array (Fin pZ.h) := (Array.ofFn id).filter fun l => !isConst l
  set mon := Real.PolyZonotope.monomial pZ.E a
  set Q := pZ.foldConstants
  -- a generator without a factor has the monomial one
  have hone : ∀ l, isConst l = true → mon l = 1 := by
    intro l hl
    have hk : ∀ k, pZ.E k l = 0 := fun k => by
      simpa using (List.all_eq_true.1 hl) k (List.mem_finRange k)
    simp [mon, Real.PolyZonotope.monomial, hk]
  -- the generator sum: the constants, and the kept generators in their order
  have hsplit : ∀ i, (∑ l, toReal (pZ.G l i) * mon l)
      = (K.map fun l => toReal (pZ.G l i)).sum
        + ∑ t : Fin keep.size, toReal (pZ.G keep[t] i) * mon keep[t] := by
    intro i
    rw [Fin.sum_univ_def, PolyZonotope.aux_sum_filter _ isConst]
    congr 1
    · exact congrArg List.sum (List.map_congr_left fun l hl => by
        rw [hone l (List.of_mem_filter hl), mul_one])
    · rw [← List.sum_ofFn (f := fun t : Fin keep.size => toReal (pZ.G keep[t] i) * mon keep[t])]
      have hk : keep.toList = (List.finRange pZ.h).filter fun l => !isConst l := by
        simp [keep, List.ofFn_id]
      congr 1
      rw [← hk]
      apply List.ext_getElem <;> simp
  -- the center's sums against the exact ones
  have hfold := fun i => PolyZonotope.aux_fold (fun l => pZ.G l i) _ (fun _ _ => rfl) K
    (pZ.c i, zero)
  set d : Fin n → ℝ := fun i =>
    toReal (pZ.c i) + (K.map fun l => toReal (pZ.G l i)).sum - toReal (Q.c i)
  refine ⟨fun i => toReal (Q.c i) + (∑ t, toReal (Q.G t i) * Real.PolyZonotope.monomial Q.E a t)
      + ∑ j : Fin Q.q, toReal (Q.GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩, fun i => d i + e i, ?_, ?_⟩
  · -- the box takes the rounding of the center's sums
    intro i
    have h₁ : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
    have hf := hfold i
    rw [toReal_zero, add_zero] at hf
    have hd := abs_le.1 (le_trans (le_refl |d i|) hf)
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry, toReal_neg]
      linarith [hd.1]
    · simp only [Entrywise.entry]
      linarith [hd.2]
  · funext i
    have hzi := hz i
    show toReal (Q.c i) + (∑ t : Fin keep.size, toReal (pZ.G keep[t] i) * mon keep[t])
        + (∑ j : Fin pZ.q, toReal (pZ.GI j i) * β j) + (d i + e i) = z i + e i
    rw [hzi, hsplit i]
    simp only [d]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
