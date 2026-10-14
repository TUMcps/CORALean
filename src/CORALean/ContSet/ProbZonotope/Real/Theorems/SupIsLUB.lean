module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Sup
public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalAttained
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `ProbZonotope.sup` is the supremum of the sup-norm over the confidence set

The box of a zonotope attains its bounds in every coordinate (`Zonotope.interval_attained`), so
the larger sup-norm of the two bounds is not only an upper bound of `‖x‖∞` over
`zonotope(probZ, m)` but its least one. Exact, as CORA's help for `sup` says; CORA's code reads
the box that ignores the deterministic generators (`supCora_lt`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.sup_isLUB (P : ProbZonotope n) (m : ℝ) :
    IsLUB ((fun x : Vec ℝ n => ‖x‖) '' (P.zonotope m).construct) (P.sup m) := by -- --- PROOF ---
  set Z := P.zonotope m
  have hI : P.interval m = Z.interval := rfl
  have hsup : P.sup m = max ‖Z.interval.inf‖ ‖Z.interval.sup‖ := by
    simp only [ProbZonotope.sup, hI]
  rw [hsup]
  have hnn : 0 ≤ max ‖Z.interval.inf‖ ‖Z.interval.sup‖ := (norm_nonneg _).trans (le_max_left _ _)
  -- an upper bound: each coordinate of a point lies between the bounds of the box
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
    have h := Z.interval_contains hx i
    have h1 : Z.interval.inf i ≤ x i := h.1
    have h2 : x i ≤ Z.interval.sup i := h.2
    have h3 : |Z.interval.inf i| ≤ max ‖Z.interval.inf‖ ‖Z.interval.sup‖ :=
      (norm_le_pi_norm Z.interval.inf i).trans (le_max_left _ _)
    have h4 : |Z.interval.sup i| ≤ max ‖Z.interval.inf‖ ‖Z.interval.sup‖ :=
      (norm_le_pi_norm Z.interval.sup i).trans (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Z.interval.inf i)]
    · linarith [le_abs_self (Z.interval.sup i)]
  -- the least one: each bound of the box is attained, so `b` is above both norms
  · intro b hb
    have hb0 : 0 ≤ b := by
      have := hb ⟨Z.c, ⟨fun _ => 0, fun _ => by simp, by simp⟩, rfl⟩
      exact (norm_nonneg _).trans this
    refine max_le ((pi_norm_le_iff_of_nonneg hb0).2 fun i => ?_)
      ((pi_norm_le_iff_of_nonneg hb0).2 fun i => ?_)
    · obtain ⟨z, hz, hzi⟩ := (Z.interval_attained i).2
      rw [Real.norm_eq_abs, ← hzi]
      exact (norm_le_pi_norm z i).trans (hb ⟨z, hz, rfl⟩)
    · obtain ⟨z, hz, hzi⟩ := (Z.interval_attained i).1
      rw [Real.norm_eq_abs, ← hzi]
      exact (norm_le_pi_norm z i).trans (hb ⟨z, hz, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
