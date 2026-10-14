module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope

CORA's `polyZonotope(taylm)`: the variables are the dependent factors, every term of every
coordinate a generator along that coordinate with the term's exponents, and each remainder
an independent generator about its centre. CORA also folds the constant terms into the
centre; here they stay generators at the zero exponent, the same set. Exact when every
remainder is a nonempty interval (`polyZonotope_exact`); the range set is always contained
(`polyZonotope_contains`), a point of it having a remainder value in each interval.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def Taylm.aux_allTerms (T : Fin m → Taylm n) : List (Fin m × (ℝ × (Fin n → ℕ))) :=
  (List.finRange m).flatMap fun i => (T i).terms.map fun a => (i, a)

noncomputable def Taylm.polyZonotope (T : Fin m → Taylm n) : PolyZonotope (Vec ℝ m) where
  p := n
  h := (Taylm.aux_allTerms T).length
  q := m
  c := fun i => ((T i).remInf + (T i).remSup) / 2
  G := fun j => Pi.single ((Taylm.aux_allTerms T).get j).1 ((Taylm.aux_allTerms T).get j).2.1
  E := fun k j => ((Taylm.aux_allTerms T).get j).2.2 k
  GI := fun l => Pi.single l (((T l).remSup - (T l).remInf) / 2)

theorem Taylm.aux_dep_apply (T : Fin m → Taylm n) (a : Vec ℝ n) (i : Fin m) :
    (∑ j, PolyZonotope.monomial (Taylm.polyZonotope T).E a j • (Taylm.polyZonotope T).G j) i
      = (T i).poly a := by -- --- PROOF ---
  rw [Finset.sum_apply]
  have hg : ∀ j : Fin (Taylm.polyZonotope T).h,
      (PolyZonotope.monomial (Taylm.polyZonotope T).E a j • (Taylm.polyZonotope T).G j) i
        = (fun x : Fin m × (ℝ × (Fin n → ℕ)) =>
            if x.1 = i then x.2.1 * Taylm.monomial x.2.2 a else 0)
          ((Taylm.aux_allTerms T).get j) := by
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
  show ∑ j : Fin (Taylm.aux_allTerms T).length, _ = _
  refine Eq.trans (key (Taylm.aux_allTerms T)
    (fun x => if x.1 = i then x.2.1 * Taylm.monomial x.2.2 a else 0)) ?_
  simp only [Taylm.aux_allTerms, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
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

theorem Taylm.aux_indep_apply (T : Fin m → Taylm n) (β : Fin (Taylm.polyZonotope T).q → ℝ)
    (i : Fin m) :
    (∑ l, β l • (Taylm.polyZonotope T).GI l) i
      = β i * (((T i).remSup - (T i).remInf) / 2) := by -- --- PROOF ---
  change (∑ l : Fin m, β l • (Pi.single l (((T l).remSup - (T l).remInf) / 2) : Vec ℝ m)) i = _
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro l _ hl; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem Taylm.polyZonotope_contains (T : Fin m → Taylm n) :
    Taylm.construct T ⊆ (Taylm.polyZonotope T).construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hx⟩
  -- the remainder values form a point of the remainder box, which its zonotope reaches
  set R : Interval (Vec ℝ m) := ⟨fun i => (T i).remInf, fun i => (T i).remSup⟩
  have hR : (fun i => x i - (T i).poly t) ∈ R.construct := fun i => hx i
  obtain ⟨β, hβ, hxβ⟩ := R.zonotope_contains hR
  refine ⟨t, β, ht, hβ, funext fun i => ?_⟩
  have hxi := congrFun hxβ i
  simp only [Interval.zonotope, R, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hxi
  rw [Pi.add_apply, Pi.add_apply, Taylm.aux_dep_apply]
  have h3 := Taylm.aux_indep_apply T β i
  erw [h3]
  simp only [Taylm.polyZonotope]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyZonotope_exact (T : Fin m → Taylm n) (hT : ∀ i, (T i).remInf ≤ (T i).remSup) :
    (Taylm.polyZonotope T).construct = Taylm.construct T := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ (Taylm.polyZonotope_contains T)
  rintro x ⟨a, β, ha, hβ, rfl⟩
  refine ⟨a, ha, fun i => ?_⟩
  rw [Pi.add_apply, Pi.add_apply, Taylm.aux_dep_apply, Taylm.aux_indep_apply]
  simp only [Taylm.polyZonotope]
  have hr : 0 ≤ ((T i).remSup - (T i).remInf) / 2 := by linarith [hT i]
  have hb := abs_le.1 (hβ i)
  constructor <;> nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
