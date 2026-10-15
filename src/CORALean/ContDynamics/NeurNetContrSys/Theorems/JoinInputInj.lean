module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The plant's input vector determines its two parts

`joinInput` places the network's part in the first `m` coordinates and the external part after
them, so neither is lost: `[a; e] = [a'; e']` forces `a = a'` and `e = e'`. This is what lets a
run of the plant under `input (π x) (v t)` hand back that `v t` lies in `U_ext`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem joinInput_inj {M m : ℕ} (hm : m ≤ M) {a a' : Vec ℝ m} {e e' : Vec ℝ (M - m)}
    (h : joinInput hm a e = joinInput hm a' e') : a = a' ∧ e = e' := by -- --- PROOF ---
  constructor
  · funext j
    have := congrFun h ⟨j.val, by omega⟩
    simpa [joinInput, j.isLt] using this
  · funext j
    have := congrFun h ⟨m + j.val, by omega⟩
    simpa [joinInput] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
