module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConvHullSingleConsIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.SumConvHullE

@[expose] public section

/-!
# What `convHullSingle` denotes

The set of [1, Prop. 9]'s construction applied to one set, before Carathéodory
is brought to bear on it: exactly the weighted sums of `a` of that set's points,
with non-negative weights summing to one.

Both halves are the same two lemmas read in opposite directions —
`mem_convHullSingle_cons_iff` splitting the constraints into the copies' own plus the
weight row, and `sum_convHullE` reading the generator sum back as a weighted sum
of points. `qI = 0` is [1, Def. 5]'s representation, as for
`linComb_exact_of_dependent`: a point of the set has to be its copy's, and an
independent generator would answer to no copy.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `convHullSingle a` denotes the weighted sums of `a` points of the set. -/
theorem ConPolyZono.convHullSingle_construct (a : ℕ) (cPZ : ConPolyZono α) (hq : cPZ.qI = 0) :
    (cPZ.convHullSingle a).construct
      = {x | ∃ y : Fin a → α, ∃ lam : Fin a → ℝ, (∀ j, y j ∈ cPZ.construct)
        ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ x = ∑ j, lam j • y j} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨v, β, hv, hβ, hsat, rfl⟩
    obtain ⟨hj, hl⟩ := (ConPolyZono.mem_convHullSingle_cons_iff a cPZ v).mp hsat
    refine ⟨fun j => cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) i • cPZ.G i,
      fun j => 1 + v (Fin.natAdd (a * cPZ.p) j), fun j => ?_, fun j => ?_, ?_, ?_⟩
    · -- block `j` is a factor vector of the set, and its point is that block's
      exact ⟨fun k => v (Fin.castAdd a (finProdFinEquiv (j, k))), fun _ => 0, fun k => hv _,
        fun _ => by simp, hj j, by simp⟩
    · linarith [abs_le.mp (hv (Fin.natAdd (a * cPZ.p) j)) |>.1]
    · -- `a` weights shifted by one, over a factor sum the last row pins
      rw [Finset.sum_add_distrib, hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      ring
    · show (a : ℝ) • cPZ.c + (∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a cPZ.E) v i
          • ConPolyZono.convHullG a cPZ.c cPZ.G i) + ∑ j : Fin 0, β j • (Fin.elim0 j : α)
        = _
      rw [ConPolyZono.sum_convHullE]
      simp
  · rintro ⟨y, lam, hy, hlam, hsum, rfl⟩
    choose aj βj haj hbj hsatj hyj using hy
    -- a weight is at most one, so the factor standing for it stays in the cube
    have hlam1 : ∀ j, lam j ≤ 1 := fun j => by
      rw [← hsum]; exact Finset.single_le_sum (fun i _ => hlam i) (Finset.mem_univ j)
    set v : Fin (a * cPZ.p + a) → ℝ := Fin.append
      (fun x => aj (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
      (fun j => lam j - 1) with hvdef
    have hvblk : ∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) = aj j :=
      fun j => funext fun k => by rw [hvdef, Fin.append_left]; simp
    have hvlam : ∀ j : Fin a, v (Fin.natAdd (a * cPZ.p) j) = lam j - 1 :=
      fun j => by rw [hvdef, Fin.append_right]
    have hGI : ∀ j, (∑ l, βj j l • cPZ.GI l) = (0 : α) := fun j =>
      Finset.sum_eq_zero fun l _ => absurd l.isLt (by omega)
    refine ⟨v, fun _ => 0, ?_, fun _ => by simp, ?_, ?_⟩
    · refine Fin.addCases (fun x => ?_) (fun j => ?_)
      · rw [hvdef, Fin.append_left]; exact haj _ _
      · rw [hvlam j, abs_le]; constructor <;> linarith [hlam j, hlam1 j]
    · -- each copy carries its own point's factors, and the weights the last row
      refine (ConPolyZono.mem_convHullSingle_cons_iff a cPZ v).mpr ⟨fun j => ?_, ?_⟩
      · rw [hvblk j]; exact hsatj j
      · rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hvlam j),
          Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
    · show (∑ j, lam j • y j) = (a : ℝ) • cPZ.c
        + (∑ i, PolyZonotope.monomial (ConPolyZono.convHullE a cPZ.E) v i
            • ConPolyZono.convHullG a cPZ.c cPZ.G i) + ∑ j : Fin 0, (0 : ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.sum_convHullE]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hyj j, hGI j, add_zero, hvlam j, hvblk j]
      congr 1
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
