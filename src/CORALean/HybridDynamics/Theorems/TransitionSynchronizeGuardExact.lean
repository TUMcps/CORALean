module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Float.Theorems.MemFullspace

@[expose] public section

/-!
# `Transition.synchronizeGuard` is the intersection, for error-free guards

When every guard's error box is certified to be the origin, and the scalar certifies
`zero = zero` (every float format does), each step of the fold only stacks rows
(`HPolytope.intersection_exact`) and leaves an origin box behind, which the next step certifies
again. So the synchronized guard denotes the intersection of the guards, with equality. For
guards with an error box, `Transition.synchronizeGuard_outer` still holds.

## Inputs
* `g` – guards of the components

## Hypotheses
* `h0` – zero is certified equal to itself
* `hg` – every guard has no error box

## Conclusion
* the synchronized guard is the intersection of the guards
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- A polytope with the origin box and certified-zero slacks passes the check, when `zero = zero`
is certified. -/
theorem aux_isErrFree_of_origin (h0 : HPolytope.eqScalar (FloatOps.zero : 𝕋) FloatOps.zero = true)
    {P : HPolytope 𝕋 (Vec 𝕋 n)} (hP : P.I_error = Interval.origin n)
    (hb : HPolytope.isZeroVec P.b_error = true) (he : HPolytope.isZeroVec P.be_error = true) :
    P.isErrFree = true := by
  rw [HPolytope.isErrFree, hb, he, hP]
  simp [HPolytope.isZeroVec, Interval.origin, h0]

omit [SoundFloatArithmetic 𝕋] in
/-- Two vectors certified zero, appended, are certified zero. -/
theorem aux_isZeroVec_append {k l : ℕ} {u : Vec 𝕋 k} {v : Vec 𝕋 l}
    (hu : HPolytope.isZeroVec u = true) (hv : HPolytope.isZeroVec v = true) : -- --- CONCL ---
    HPolytope.isZeroVec (Fin.append u v) = true := by -- --- PROOF ---
  simp only [HPolytope.isZeroVec, List.all_eq_true, List.mem_finRange, true_implies] at hu hv ⊢
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact hu i
  · rw [Fin.append_right]; exact hv i

/-- The accumulator of the guard fold stays error-free and is the intersection so far. -/
theorem aux_synchronizeGuard_fold_eq
    (h0 : HPolytope.eqScalar (FloatOps.zero : 𝕋) FloatOps.zero = true)
    (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) (hg : ∀ i, (g i).isErrFree = true) (l : List (Fin q))
    (P : HPolytope 𝕋 (Vec 𝕋 n)) (hP : P.isErrFree = true) : -- --- CONCL ---
    (l.foldl (fun guard i => HPolytope.intersection guard (g i)) P).construct =
      P.construct ∩ ⋂ i ∈ l, (g i).construct := by -- --- PROOF ---
  induction l generalizing P with
  | nil => simp
  | cons a l ih =>
    -- one step only stacks the rows, which leaves the origin box
    have hstep : (P.intersection (g a)).isErrFree = true := by
      rw [HPolytope.intersection, if_pos (by rw [hP, hg a]; rfl)]
      have hP' := hP
      have hg' := hg a
      simp only [HPolytope.isErrFree, Bool.and_eq_true] at hP' hg'
      exact aux_isErrFree_of_origin h0 rfl (aux_isZeroVec_append hP'.2.1 hg'.2.1)
        (aux_isZeroVec_append hP'.2.2 hg'.2.2)
    rw [List.foldl_cons, ih _ hstep, ← HPolytope.intersection_exact hP (hg a)]
    ext x
    simp [and_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The synchronized guard denotes the intersection of the guards: exact. -/
theorem Transition.synchronizeGuard_exact
    (h0 : HPolytope.eqScalar (FloatOps.zero : 𝕋) FloatOps.zero = true)
    (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) (hg : ∀ i, (g i).isErrFree = true) : -- --- CONCL ---
    (Transition.synchronizeGuard g).construct = ⋂ i, (g i).construct := by -- --- PROOF ---
  unfold Transition.synchronizeGuard
  rw [aux_synchronizeGuard_fold_eq h0 g hg _ _ (aux_isErrFree_of_origin h0 rfl
    (by simp [HPolytope.isZeroVec, HPolytope.fullspace])
    (by simp [HPolytope.isZeroVec, HPolytope.fullspace]))]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, List.mem_finRange, forall_true_left]
  exact ⟨fun h => h.2, fun h => ⟨HPolytope.mem_fullspace x, h⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
