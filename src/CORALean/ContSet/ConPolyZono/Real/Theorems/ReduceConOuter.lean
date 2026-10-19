module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceCon
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `ConPolyZono.reduceCon` over-approximates the set

The operation and its guarantee are [1, Prop. 13]. Constraint row `r` reads
`A(r,t) μ_t(α) + Σ_{i ≠ t} A(r,i) μ_i(α) = b(r)`, which solves for `μ_t(α)`
whenever `A(r,t) ≠ 0`; eq. (33)'s other half, that generator `d` carries the
same exponent column as constraint generator `t`, is what makes that solution
land in the generator sum as well as in the constraints.

An enclosure and not an equality, and the asymmetry is the substitution's: every
factor vector the original admits satisfies the reduced system with the same
value, but a factor vector of the reduced system need not put `μ_t(α)` where row
`r` would have. Nothing here compensates for that, and [1] claims nothing more.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `reduceCon`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem ConPolyZono.aux_sum_univ_reduceCon (cPZ : ConPolyZono α) (r : Fin cPZ.cons.m)
    (d : Fin cPZ.h) (t : Fin cPZ.cons.q) (a : Fin cPZ.p → ℝ) : -- --- STMT ---
    ∑ i : Fin (cPZ.reduceCon r d t).h,
        PolyZonotope.monomial (cPZ.reduceCon r d t).E a i • (cPZ.reduceCon r d t).G i
      = ∑ i : Fin (cPZ.h - 1), PolyZonotope.monomial cPZ.E a (dropIdx d i) • cPZ.G (dropIdx d i)
        + ∑ i : Fin (cPZ.cons.q - 1), PolyZonotope.monomial cPZ.cons.R a (dropIdx t i)
            • ((-(cPZ.cons.A r (dropIdx t i)) / cPZ.cons.A r t) • cPZ.G d) := by -- --- PROOF ---
  refine (Fin.sum_univ_add (f := fun i : Fin ((cPZ.h - 1) + (cPZ.cons.q - 1)) =>
    PolyZonotope.monomial (ConPolyZono.reduceConE cPZ.E cPZ.cons.R d t) a i
      • ConPolyZono.reduceConG cPZ.G cPZ.cons.A r d t i)).trans ?_
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp [PolyZonotope.monomial, ConPolyZono.reduceConE, ConPolyZono.reduceConG]
  · exact Finset.sum_congr rfl fun i _ => by
      simp [PolyZonotope.monomial, ConPolyZono.reduceConE, ConPolyZono.reduceConG]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Eliminating a constraint keeps every point: the same factors satisfy the
reduced system and give the same value. -/
theorem ConPolyZono.reduceCon_outer (cPZ : ConPolyZono α) (r : Fin cPZ.cons.m) (d : Fin cPZ.h)
    (t : Fin cPZ.cons.q) (hE : ∀ k, cPZ.E k d = cPZ.cons.R k t) (hA : cPZ.cons.A r t ≠ 0) :
    cPZ.construct ⊆ (cPZ.reduceCon r d t).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, hsat, rfl⟩
  rw [PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq] at hsat
  set μ := PolyZonotope.monomial cPZ.cons.R a with hμ
  set ν := PolyZonotope.monomial cPZ.E a with hν
  -- eq. (33): generator `d` and constraint generator `t` are the same monomial
  have hmt : ν d = μ t := by
    simp only [hμ, hν, PolyZonotope.monomial]
    exact Finset.prod_congr rfl fun k _ => by rw [hE k]
  have hrow : ∑ i, cPZ.cons.A r i * μ i = cPZ.cons.b r := hsat r
  -- eq. (35), read as what the surviving constraint generators sum to
  have hrest : ∑ i : Fin (cPZ.cons.q - 1), cPZ.cons.A r (dropIdx t i) * μ (dropIdx t i)
      = cPZ.cons.b r - cPZ.cons.A r t * μ t := by
    rw [← hrow, sum_dropIdx t (fun i => cPZ.cons.A r i * μ i)]
    ring
  refine ⟨a, β, ha, hβ, (PolyLevelSet.mem_construct_iff_of_eq (cPZ.reduceCon r d t).cons_eq).mpr ?_,
    ?_⟩
  -- eq. (36): every surviving row holds, its right-hand side shifted
  · intro j
    have hJ : ∑ i : Fin (cPZ.cons.q - 1), cPZ.cons.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
        = (cPZ.cons.A *ᵥ μ) (dropIdx r j) - cPZ.cons.A (dropIdx r j) t * μ t := by
      have hmv : (cPZ.cons.A *ᵥ μ) (dropIdx r j) = ∑ i, cPZ.cons.A (dropIdx r j) i * μ i := rfl
      rw [hmv, sum_dropIdx t (fun i => cPZ.cons.A (dropIdx r j) i * μ i)]
      ring
    -- the reduced row, before the rank-one correction is split off it
    have hsum : ((cPZ.reduceCon r d t).cons.A
        *ᵥ PolyZonotope.monomial (cPZ.reduceCon r d t).cons.R a) j
        = ∑ i : Fin (cPZ.cons.q - 1),
            (cPZ.cons.A (dropIdx r j) (dropIdx t i)
              - cPZ.cons.A r (dropIdx t i) * cPZ.cons.A (dropIdx r j) t / cPZ.cons.A r t)
                  * μ (dropIdx t i) :=
      rfl
    have hterm : ∀ i : Fin (cPZ.cons.q - 1),
        (cPZ.cons.A (dropIdx r j) (dropIdx t i)
            - cPZ.cons.A r (dropIdx t i) * cPZ.cons.A (dropIdx r j) t / cPZ.cons.A r t)
                * μ (dropIdx t i)
          = cPZ.cons.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
            - cPZ.cons.A (dropIdx r j) t / cPZ.cons.A r t
              * (cPZ.cons.A r (dropIdx t i) * μ (dropIdx t i)) := fun i => by ring
    -- so the row is the original one, shifted by exactly what `reduceConB` shifts
    have hval : ((cPZ.reduceCon r d t).cons.A
        *ᵥ PolyZonotope.monomial (cPZ.reduceCon r d t).cons.R a) j
        = (cPZ.cons.A *ᵥ μ) (dropIdx r j) - cPZ.cons.b r
            * cPZ.cons.A (dropIdx r j) t / cPZ.cons.A r t := by
      rw [hsum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, hJ, hrest]
      field_simp
      ring
    rw [hval, hsat (dropIdx r j)]
    rfl
  -- the value: generator `d`'s term is what the center and the new block replace
  · have hsplitG : ∑ i, ν i • cPZ.G i
        = ν d • cPZ.G d + ∑ i : Fin (cPZ.h - 1), ν (dropIdx d i) • cPZ.G (dropIdx d i) :=
      sum_dropIdx d (fun i => ν i • cPZ.G i)
    have hres : ∑ i : Fin (cPZ.reduceCon r d t).h,
          PolyZonotope.monomial (cPZ.reduceCon r d t).E a i • (cPZ.reduceCon r d t).G i
        = ∑ i : Fin (cPZ.h - 1), ν (dropIdx d i) • cPZ.G (dropIdx d i)
          + ∑ i : Fin (cPZ.cons.q - 1),
              μ (dropIdx t i) • ((-(cPZ.cons.A r (dropIdx t i)) / cPZ.cons.A r t) • cPZ.G d) := by
      rw [hν, hμ]
      exact ConPolyZono.aux_sum_univ_reduceCon cPZ r d t a
    -- the new block is one scalar multiple of `G d`, so it sums as one
    have hterm : ∀ i : Fin (cPZ.cons.q - 1),
        μ (dropIdx t i) • ((-(cPZ.cons.A r (dropIdx t i)) / cPZ.cons.A r t) • cPZ.G d)
          = (-(1 / cPZ.cons.A r t) * (cPZ.cons.A r (dropIdx t i) * μ (dropIdx t i))) • cPZ.G d := by
      intro i
      rw [smul_smul]
      congr 1
      field_simp
    have hsum2 : ∑ i : Fin (cPZ.cons.q - 1),
          μ (dropIdx t i) • ((-(cPZ.cons.A r (dropIdx t i)) / cPZ.cons.A r t) • cPZ.G d)
        = (-(1 / cPZ.cons.A r t) * (cPZ.cons.b r - cPZ.cons.A r t * μ t)) • cPZ.G d := by
      simp only [hterm, ← Finset.sum_smul, ← Finset.mul_sum, hrest]
    -- and that multiple, with the center's, is generator `d`'s own monomial back
    have hcenter : ν d • cPZ.G d
        = (cPZ.cons.b r / cPZ.cons.A r t) • cPZ.G d
          + (-(1 / cPZ.cons.A r t) * (cPZ.cons.b r - cPZ.cons.A r t * μ t)) • cPZ.G d := by
      rw [← add_smul, hmt]
      congr 1
      field_simp
      ring
    rw [hsplitG, hres, hsum2, hcenter]
    show _ = cPZ.c + (cPZ.cons.b r / cPZ.cons.A r t) • cPZ.G d + _ + _
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
