import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Taylm.Float.Taylm

/-!
# An array of Taylor models as a polynomial zonotope, over a floating-point scalar

CORA's `polyZonotope(taylm)`: the variables are the dependent factors, every term of every
coordinate a generator along that coordinate, and the remainders independent. The centre is `0`
and the constant terms stay generators at the zero exponent. The remainder box `[remInf, remSup]`
is carried over as the error box, so nothing rounds, no midpoint is formed and nothing is paid.
The range set is contained; an inverted remainder is `∅` on both sides, so no hypothesis is
needed here.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every term of every coordinate, tagged with the coordinate it belongs to. -/
def Taylm.aux_allTerms (T : Fin m → Taylm 𝕋 n) : List (Fin m × (𝕋 × (Fin n → ℕ))) :=
  (List.finRange m).flatMap fun i => (T i).terms.map fun a => (i, a)


def Taylm.polyZonotope (T : Fin m → Taylm 𝕋 n) : PolyZonotope 𝕋 m where
  p := n
  h := (Taylm.aux_allTerms T).length
  q := 0
  c := fun _ => zero
  G := fun j i => if ((Taylm.aux_allTerms T).get j).1 = i then ((Taylm.aux_allTerms T).get j).2.1
    else zero
  E := fun k j => ((Taylm.aux_allTerms T).get j).2.2 k
  GI := Fin.elim0
  err := ⟨fun i => (T i).remInf, fun i => (T i).remSup⟩

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent part of the polynomial zonotope is the polynomial of each coordinate. -/
theorem Taylm.aux_dep_apply (T : Fin m → Taylm 𝕋 n) (t : Vec ℝ n) (i : Fin m) :
    ∑ l, toReal ((Taylm.polyZonotope T).G l i) *
        Real.PolyZonotope.monomial (Taylm.polyZonotope T).E t l
      = (T i).nominal.poly t := by -- --- PROOF ---
  -- each summand is nonzero only for the terms of coordinate `i`
  have hg : ∀ j : Fin (Taylm.aux_allTerms T).length,
      toReal ((Taylm.polyZonotope T).G j i) *
        Real.PolyZonotope.monomial (Taylm.polyZonotope T).E t j
        = (fun x : Fin m × (𝕋 × (Fin n → ℕ)) =>
            if x.1 = i then toReal x.2.1 * Real.Taylm.monomial x.2.2 t else 0)
          ((Taylm.aux_allTerms T).get j) := by
    intro j
    simp only [Taylm.polyZonotope, Real.PolyZonotope.monomial, Real.Taylm.monomial]
    split_ifs
    · rfl
    · simp [toReal_zero]
  change ∑ j : Fin (Taylm.aux_allTerms T).length, _ = _
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hg j) ?_
  -- a sum over the generator indices is a sum over the term list
  have key : ∀ (L : List (Fin m × (𝕋 × (Fin n → ℕ)))) (g : Fin m × (𝕋 × (Fin n → ℕ)) → ℝ),
      ∑ j : Fin L.length, g (L.get j) = (L.map g).sum := by
    intro L g
    rw [← List.sum_ofFn]
    congr 1
    exact List.ext_get (by simp) fun k h1 h2 => by simp
  refine Eq.trans (key (Taylm.aux_allTerms T)
    (fun x => if x.1 = i then toReal x.2.1 * Real.Taylm.monomial x.2.2 t else 0)) ?_
  simp only [Taylm.aux_allTerms, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  -- coordinate `i` collects exactly the terms of model `i`
  have hrow : ∀ i' : Fin m, (List.sum ∘
      (List.map fun x : Fin m × (𝕋 × (Fin n → ℕ)) =>
        if x.1 = i then toReal x.2.1 * Real.Taylm.monomial x.2.2 t else 0) ∘ fun i' =>
          List.map (fun b => (i', b)) (T i').terms) i'
      = if i' = i then (T i).nominal.poly t else 0 := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp [Taylm.nominal, Real.Taylm.poly, Real.Taylm.polyOf, Function.comp_def]
    · simp [h, Function.comp_def]
  rw [List.map_congr_left fun i' _ => hrow i', ← List.ofFn_eq_map, List.sum_ofFn]
  simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyZonotope_contains (T : Fin m → Taylm 𝕋 n) :
    Taylm.construct T ⊆ (Taylm.polyZonotope T).construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hx⟩
  -- the polynomial values are the nominal part, the rest of `x` is a point of the error box
  refine ⟨fun i => (T i).nominal.poly t, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨t, Fin.elim0, ht, fun j => j.elim0, fun i => ?_⟩, fun i => x i - (T i).nominal.poly t,
    fun i => hx i, funext fun i => by simp⟩
  show (T i).nominal.poly t = toReal (zero : 𝕋) +
    ∑ l, toReal ((Taylm.polyZonotope T).G l i) *
      Real.PolyZonotope.monomial (Taylm.polyZonotope T).E t l + ∑ j : Fin 0, _
  rw [Taylm.aux_dep_apply, toReal_zero]
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
