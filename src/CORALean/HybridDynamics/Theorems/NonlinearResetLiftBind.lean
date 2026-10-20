module

public import CORALean.HybridDynamics.Theorems.NonlinearResetLiftOfNotMem
public import CORALean.HybridDynamics.Theorems.NonlinearResetFoldlUpdateOfNotMem
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# `NonlinearReset.lift` restricted to the bound coordinates is the old reset

For an injective `stateBind`, the lifted reset at coordinate `stateBind j` is the old reset at `j`
of the bound state and input: the exactness statement for CORA's `lift`.

## Inputs
* `r` – reset
* `stateBind` – state index map
* `inputBind` – input index map
* `id` – identity outside the bound states
* `x` – state of the larger space
* `u` – input of the larger space
* `j` – bound coordinate

## Hypotheses
* `hinj` – index map injective

## Conclusion
* lifted reset at a bound coordinate is the old reset
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N M : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A fold of updates along a duplicate-free list writes each coordinate's own value. -/
theorem NonlinearReset.aux_foldl_update_mem {g : Fin n → Fin N} (hg : Function.Injective g)
    (v : Fin n → ℝ) (j : Fin n) : -- --- CONCL ---
    ∀ (l : List (Fin n)) (base : Fin N → ℝ), l.Nodup → j ∈ l →
      l.foldl (fun acc k => Function.update acc (g k) (v k)) base (g j) = v j := by -- --- PROOF ---
  -- induction on the list: `j` is the head, whose update no later one overwrites, or later
  intro l
  induction l with
  | nil => intro _ _ h; exact absurd h List.not_mem_nil
  | cons a l ih =>
    intro base hnd hj
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hj with rfl | hjl
    · rw [NonlinearReset.foldl_update_of_not_mem g v (g j) l _ fun k hk h =>
        hnd.1 (hg h ▸ hk), Function.update_self]
    · exact ih _ hnd.2 hjl


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.lift_evaluate_bind (r : NonlinearReset n m n)
    (stateBind : Fin n → Fin N) (hinj : Function.Injective stateBind)
    (inputBind : Fin m → Fin M) (id : Bool) (x : Vec ℝ N) (u : Vec ℝ M)
    (j : Fin n) : -- --- CONCL ---
    (r.lift N M stateBind inputBind id).evaluate x u (stateBind j) =
      r.evaluate (fun k => x (stateBind k)) (fun k => u (inputBind k)) j := by -- --- PROOF ---
  exact NonlinearReset.aux_foldl_update_mem hinj _ j _ _ (List.nodup_finRange n)
    (List.mem_finRange j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
