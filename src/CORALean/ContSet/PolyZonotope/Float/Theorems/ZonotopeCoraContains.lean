module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ZonotopeCora
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `PolyZonotope.zonotopeCora` encloses the set

The exact layer's coefficients (`2m - 1` on an all-even column, whose monomial `m` is in
`[0, 1]`, the monomial otherwise) are admissible and reproduce the dependent sum with the
centre's share; the halved generators are exact, and the centre's rounding `c + s - cLo ≥ 0` is
at most the gap added to the top of the error box. Outer, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotopeCora_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.zonotopeCora.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  -- the centre's share of each generator, and what the centre's rounding leaves out
  set s : Fin pZ.h → Vec 𝕋 n := fun l i =>
    if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else zero with hs
  set d : Vec ℝ n := fun i => toReal (pZ.c i) + ∑ l, toReal (s l i)
    - toReal (addDown (pZ.c i) (sumDown fun l => s l i)) with hd
  -- the free half's coefficient: `2m - 1` on an all-even column, the monomial otherwise
  set b : Fin pZ.h → ℝ := fun l => if ∀ k, pZ.E k l % 2 = 0
    then 2 * Real.PolyZonotope.monomial pZ.E a l - 1 else Real.PolyZonotope.monomial pZ.E a l
    with hb
  have hterm : ∀ i l, toReal (if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i)
      * b l + toReal (s l i) = toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l :=
    fun i l => by
      simp only [hs, hb]
      split_ifs <;> simp only [toReal_half, toReal_zero] <;> ring
  refine ⟨z - d, Zonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append b β, ?_, fun i => ?_⟩,
    e + d, fun i => ⟨?_, ?_⟩, by ring⟩
  · -- the coefficients are in `[-1, 1]`
    refine Fin.addCases (fun l => ?_) fun j => ?_
    · have hm := abs_le.mp (Real.PolyZonotope.abs_monomial_le_one pZ.E ha l)
      simp only [Fin.append_left, hb]
      split_ifs with he
      · -- an all-even monomial is in `[0, 1]`
        have h0 : 0 ≤ Real.PolyZonotope.monomial pZ.E a l :=
          Finset.prod_nonneg fun k _ => Even.pow_nonneg (Nat.even_iff.mpr (he k)) (a k)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exact abs_le.mpr hm
    · simpa using hβ j
  · -- the generators, dependent then independent, at those coefficients
    show z i - d i = toReal (addDown (pZ.c i) (sumDown fun l => s l i))
      + ∑ l : Fin (pZ.h + pZ.q), toReal (Fin.append (fun l i =>
          if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else pZ.G l i) pZ.GI l i)
        * Fin.append b β l
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hsum := Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hterm i l
    rw [Finset.sum_add_distrib] at hsum
    rw [hz i, hd]
    simp only
    linarith
  · -- the rounded-down centre is below the exact one
    have h1 := addDown_le_add (pZ.c i) (sumDown fun l => s l i)
    have h2 := sumDown_le_sum fun l => s l i
    have he1 : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
    show toReal (pZ.I_error.inf i) ≤ e i + d i
    simp only [hd]
    linarith
  · -- the rounding gap bounds `d` above
    have h1 := add_le_addUp (pZ.c i) (sumUp fun l => s l i)
    have h2 := sum_le_sumUp fun l => s l i
    have h3 := sub_le_subUp (addUp (pZ.c i) (sumUp fun l => s l i))
      (addDown (pZ.c i) (sumDown fun l => s l i))
    have h4 := add_le_addUp (pZ.I_error.sup i) (subUp (addUp (pZ.c i) (sumUp fun l => s l i))
      (addDown (pZ.c i) (sumDown fun l => s l i)))
    have he2 : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
    show e i + d i ≤ toReal (addUp (pZ.I_error.sup i) (subUp (addUp (pZ.c i) (sumUp fun l => s l i))
      (addDown (pZ.c i) (sumDown fun l => s l i))))
    simp only [hd]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
