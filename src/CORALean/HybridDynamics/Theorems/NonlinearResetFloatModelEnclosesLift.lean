import CORALean.HybridDynamics.Operations.NonlinearResetLiftFloat
import CORALean.HybridDynamics.Theorems.NonlinearResetLiftBind
import CORALean.HybridDynamics.Theorems.NonlinearResetLiftOfNotMem
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate

/-!
# The lifted float model encloses the lifted reset

If `fm` encloses `r`, then `fm.lift` encloses `r.lift`, for an injective `stateBind` (the case the
real `lift_evaluate_bind` is stated for): a bound coordinate takes the old reset's box, and any
other keeps its box or is the origin. An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m N M : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.FloatModel.Encloses.lift {fm : NonlinearReset.FloatModel 𝕋 n m n}
    {r : NonlinearReset n m n} (h : fm.Encloses r) (stateBind : Fin n → Fin N)
    (hinj : Function.Injective stateBind) (inputBind : Fin m → Fin M) (id : Bool) :
    (fm.lift N M stateBind inputBind id).Encloses
      (r.lift N M stateBind inputBind id) := by -- --- PROOF ---
  refine ⟨fun X U x hx u hu => ?_⟩
  -- a vector is in a float box when every coordinate is between the real bounds
  have mem_iff : ∀ {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec ℝ k),
      v ∈ construct I ↔ ∀ i, toReal (I.inf i) ≤ v i ∧ v i ≤ toReal (I.sup i) :=
    fun _ _ => Iff.rfl
  rw [mem_iff] at hx hu ⊢
  -- the old reset reads the bound coordinates of the boxes, which hold the bound coordinates
  have hY := (mem_iff _ _).1 (h.f_mem ⟨fun j => X.inf (stateBind j), fun j => X.sup (stateBind j)⟩
    ⟨fun k => U.inf (inputBind k), fun k => U.sup (inputBind k)⟩
    (fun j => x (stateBind j)) ((mem_iff _ _).2 fun j => hx (stateBind j))
    (fun k => u (inputBind k)) ((mem_iff _ _).2 fun k => hu (inputBind k)))
  intro i
  unfold NonlinearReset.FloatModel.lift
  dsimp only
  -- the last old coordinate written to `i`, if any
  rcases hsrc : (List.finRange n).reverse.find? (fun j => stateBind j == i) with _ | j
  · -- no coordinate is bound to `i`: its box, or the origin
    have hi : ∀ j, stateBind j ≠ i := fun j hj =>
      (List.find?_eq_none.mp hsrc) j (List.mem_reverse.mpr (List.mem_finRange j))
        (by simpa using hj)
    have hv := NonlinearReset.lift_evaluate_of_not_mem r stateBind inputBind id x u i hi
    have hv' : (r.lift N M stateBind inputBind id).f x u i = if id then x i else 0 := hv
    rw [hv']
    cases id
    · simp [toReal_zero]
    · simpa using hx i
  · -- coordinate `j` is bound to `i`: the old reset's `j`-th box
    have hj : stateBind j = i := by simpa using List.find?_some hsrc
    subst hj
    have hv := NonlinearReset.lift_evaluate_bind r stateBind hinj inputBind id x u j
    have hv' : (r.lift N M stateBind inputBind id).f x u (stateBind j) =
        r.f (fun k => x (stateBind k)) (fun k => u (inputBind k)) j := hv
    rw [hv']
    exact hY j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
