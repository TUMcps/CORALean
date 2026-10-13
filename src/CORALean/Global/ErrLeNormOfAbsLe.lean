module

public import CORALean.Global.Err

@[expose] public section

/-!
# `err` against a coordinatewise bound on magnitudes

If every point of `S` is bounded in magnitude by `m`, coordinate by coordinate, then
`err S ≤ ‖m‖₂`. This is the route a float upper bound on the Euclidean `err` takes: the
magnitudes `m` are what a float zonotope's `absBoundError` holds, and `‖m‖₂` is what
`normUp` bounds from above. `err_le_of_forall_norm₂_le` loses a factor `√n` against this one,
reading each coordinate's reach as the whole vector's.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Squaring is monotone on magnitudes, so a coordinatewise bound on magnitudes is a bound on
the Euclidean norm. -/
theorem aux_norm₂_le_of_abs_le_err {x y : Vec ℝ n} (h : ∀ i, |x i| ≤ |y i|) : ‖x‖₂ ≤ ‖y‖₂ := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hi := mul_self_le_mul_self (abs_nonneg (x i)) (h i)
  rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at hi


-- =======================================  MAIN THEOREM  ======================================= --

/-- A coordinatewise bound on the magnitudes of `S` is a Euclidean bound on `err S`. -/
theorem err_le_norm₂_of_forall_abs_le {S : Set (Vec ℝ n)} {m : Vec ℝ n}
    (h : ∀ y ∈ S, ∀ i, |y i| ≤ |m i|) : err S ≤ ‖m‖₂ := by -- --- PROOF ---
  refine aux_norm₂_le_of_abs_le_err fun i => ?_
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
  rcases Set.eq_empty_or_nonempty S with hS | ⟨y0, hy0⟩
  · simp [hS, Real.sSup_empty, Real.sInf_empty]
  -- both endpoints of the box at `i` are values of `S`-points at `i`, so `h` reaches
  have hA : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, z ≤ |m i| := by
    rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (h y hy i)
  have hB : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, -|m i| ≤ z := by
    rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (h y hy i)).1
  have hbA : BddAbove ((fun x : Vec ℝ n => x i) '' S) := ⟨|m i|, hA⟩
  have hbB : BddBelow ((fun x : Vec ℝ n => x i) '' S) := ⟨-|m i|, hB⟩
  have hmemi : y0 i ∈ (fun x : Vec ℝ n => x i) '' S := ⟨y0, hy0, rfl⟩
  have hsup_le : sSup ((fun x : Vec ℝ n => x i) '' S) ≤ |m i| := csSup_le ⟨y0 i, hmemi⟩ hA
  have hsup_ge : -|m i| ≤ sSup ((fun x : Vec ℝ n => x i) '' S) :=
    (hB (y0 i) hmemi).trans (le_csSup hbA hmemi)
  have hinf_ge : -|m i| ≤ sInf ((fun x : Vec ℝ n => x i) '' S) := le_csInf ⟨y0 i, hmemi⟩ hB
  have hinf_le : sInf ((fun x : Vec ℝ n => x i) '' S) ≤ |m i| :=
    (csInf_le hbB hmemi).trans (hA (y0 i) hmemi)
  exact max_le (abs_le.mpr ⟨hsup_ge, hsup_le⟩) (abs_le.mpr ⟨hinf_ge, hinf_le⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
