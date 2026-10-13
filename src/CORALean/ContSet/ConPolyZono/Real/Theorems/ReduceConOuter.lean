module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceCon
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

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

The third hypothesis is the representation's, not [1]'s: `b` is an `Interval`
where [1, Def. 5] has a vector, and a row solved for a monomial must be a point
to determine one. Only the eliminated row is asked for it.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `reduceCon`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem ConPolyZono.aux_sum_univ_reduceCon (cPZ : ConPolyZono α) (r : Fin cPZ.m)
    (d : Fin cPZ.h) (t : Fin cPZ.s) (a : Fin cPZ.p → ℝ) :
    ∑ i : Fin (cPZ.reduceCon r d t).h,
        PolyZonotope.monomial (cPZ.reduceCon r d t).E a i • (cPZ.reduceCon r d t).G i
      = ∑ i : Fin (cPZ.h - 1), PolyZonotope.monomial cPZ.E a (dropIdx d i) • cPZ.G (dropIdx d i)
        + ∑ i : Fin (cPZ.s - 1), PolyZonotope.monomial cPZ.EC a (dropIdx t i)
            • ((-(cPZ.A r (dropIdx t i)) / cPZ.A r t) • cPZ.G d) := by -- --- PROOF ---
  refine (Fin.sum_univ_add (f := fun i : Fin ((cPZ.h - 1) + (cPZ.s - 1)) =>
    PolyZonotope.monomial (ConPolyZono.reduceConE cPZ.E cPZ.EC d t) a i
      • ConPolyZono.reduceConG cPZ.G cPZ.A r d t i)).trans ?_
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp [PolyZonotope.monomial, ConPolyZono.reduceConE, ConPolyZono.reduceConG]
  · exact Finset.sum_congr rfl fun i _ => by
      simp [PolyZonotope.monomial, ConPolyZono.reduceConE, ConPolyZono.reduceConG]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Eliminating a constraint keeps every point: the same factors satisfy the
reduced system and give the same value. -/
theorem ConPolyZono.reduceCon_outer (cPZ : ConPolyZono α) (r : Fin cPZ.m) (d : Fin cPZ.h)
    (t : Fin cPZ.s) (hE : ∀ k, cPZ.E k d = cPZ.EC k t) (hA : cPZ.A r t ≠ 0)
    (hb : cPZ.b.inf r = cPZ.b.sup r) :
    cPZ.construct ⊆ (cPZ.reduceCon r d t).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, hsat, rfl⟩
  set μ := PolyZonotope.monomial cPZ.EC a with hμ
  set ν := PolyZonotope.monomial cPZ.E a with hν
  -- eq. (33): generator `d` and constraint generator `t` are the same monomial
  have hmt : ν d = μ t := by
    simp only [hμ, hν, PolyZonotope.monomial]
    exact Finset.prod_congr rfl fun k _ => by rw [hE k]
  have hrow : ∑ i, cPZ.A r i * μ i = cPZ.b.inf r := by
    have h1 := hsat r
    have h2 : (cPZ.A *ᵥ μ) r = ∑ i, cPZ.A r i * μ i := rfl
    rw [h2, ← hb] at h1
    linarith [h1.1, h1.2]
  -- eq. (35), read as what the surviving constraint generators sum to
  have hrest : ∑ i : Fin (cPZ.s - 1), cPZ.A r (dropIdx t i) * μ (dropIdx t i)
      = cPZ.b.inf r - cPZ.A r t * μ t := by
    rw [← hrow, sum_dropIdx t (fun i => cPZ.A r i * μ i)]
    ring
  refine ⟨a, β, ha, hβ, ?_, ?_⟩
  -- eq. (36): every surviving row holds, its right-hand side shifted
  · intro j
    have hJ : ∑ i : Fin (cPZ.s - 1), cPZ.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
        = (cPZ.A *ᵥ μ) (dropIdx r j) - cPZ.A (dropIdx r j) t * μ t := by
      have hmv : (cPZ.A *ᵥ μ) (dropIdx r j) = ∑ i, cPZ.A (dropIdx r j) i * μ i := rfl
      rw [hmv, sum_dropIdx t (fun i => cPZ.A (dropIdx r j) i * μ i)]
      ring
    -- the reduced row, before the rank-one correction is split off it
    have hsum : ((cPZ.reduceCon r d t).A *ᵥ PolyZonotope.monomial (cPZ.reduceCon r d t).EC a) j
        = ∑ i : Fin (cPZ.s - 1),
            (cPZ.A (dropIdx r j) (dropIdx t i)
              - cPZ.A r (dropIdx t i) * cPZ.A (dropIdx r j) t / cPZ.A r t) * μ (dropIdx t i) :=
      rfl
    have hterm : ∀ i : Fin (cPZ.s - 1),
        (cPZ.A (dropIdx r j) (dropIdx t i)
            - cPZ.A r (dropIdx t i) * cPZ.A (dropIdx r j) t / cPZ.A r t) * μ (dropIdx t i)
          = cPZ.A (dropIdx r j) (dropIdx t i) * μ (dropIdx t i)
            - cPZ.A (dropIdx r j) t / cPZ.A r t
              * (cPZ.A r (dropIdx t i) * μ (dropIdx t i)) := fun i => by ring
    -- so the row is the original one, shifted by exactly what `reduceConB` shifts
    have hval : ((cPZ.reduceCon r d t).A *ᵥ PolyZonotope.monomial (cPZ.reduceCon r d t).EC a) j
        = (cPZ.A *ᵥ μ) (dropIdx r j) - cPZ.b.inf r * cPZ.A (dropIdx r j) t / cPZ.A r t := by
      rw [hsum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, hJ, hrest]
      field_simp
      ring
    have hbJ := hsat (dropIdx r j)
    rw [hval]
    exact ⟨by simp only [ConPolyZono.reduceCon, ConPolyZono.reduceConB]; linarith [hbJ.1],
      by simp only [ConPolyZono.reduceCon, ConPolyZono.reduceConB]; linarith [hbJ.2]⟩
  -- the value: generator `d`'s term is what the centre and the new block replace
  · have hsplitG : ∑ i, ν i • cPZ.G i
        = ν d • cPZ.G d + ∑ i : Fin (cPZ.h - 1), ν (dropIdx d i) • cPZ.G (dropIdx d i) :=
      sum_dropIdx d (fun i => ν i • cPZ.G i)
    have hres : ∑ i : Fin (cPZ.reduceCon r d t).h,
          PolyZonotope.monomial (cPZ.reduceCon r d t).E a i • (cPZ.reduceCon r d t).G i
        = ∑ i : Fin (cPZ.h - 1), ν (dropIdx d i) • cPZ.G (dropIdx d i)
          + ∑ i : Fin (cPZ.s - 1),
              μ (dropIdx t i) • ((-(cPZ.A r (dropIdx t i)) / cPZ.A r t) • cPZ.G d) := by
      rw [hν, hμ]
      exact ConPolyZono.aux_sum_univ_reduceCon cPZ r d t a
    -- the new block is one scalar multiple of `G d`, so it sums as one
    have hterm : ∀ i : Fin (cPZ.s - 1),
        μ (dropIdx t i) • ((-(cPZ.A r (dropIdx t i)) / cPZ.A r t) • cPZ.G d)
          = (-(1 / cPZ.A r t) * (cPZ.A r (dropIdx t i) * μ (dropIdx t i))) • cPZ.G d := by
      intro i
      rw [smul_smul]
      congr 1
      field_simp
    have hsum2 : ∑ i : Fin (cPZ.s - 1),
          μ (dropIdx t i) • ((-(cPZ.A r (dropIdx t i)) / cPZ.A r t) • cPZ.G d)
        = (-(1 / cPZ.A r t) * (cPZ.b.inf r - cPZ.A r t * μ t)) • cPZ.G d := by
      simp only [hterm, ← Finset.sum_smul, ← Finset.mul_sum, hrest]
    -- and that multiple, with the centre's, is generator `d`'s own monomial back
    have hcentre : ν d • cPZ.G d
        = (cPZ.b.inf r / cPZ.A r t) • cPZ.G d
          + (-(1 / cPZ.A r t) * (cPZ.b.inf r - cPZ.A r t * μ t)) • cPZ.G d := by
      rw [← add_smul, hmt]
      congr 1
      field_simp
      ring
    rw [hsplitG, hres, hsum2, hcentre]
    show _ = cPZ.c + (cPZ.b.inf r / cPZ.A r t) • cPZ.G d + _ + _
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
