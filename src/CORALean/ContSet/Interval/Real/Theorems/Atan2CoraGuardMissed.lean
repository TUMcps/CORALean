import CORALean.ContSet.Interval.Real.Operations.Atan2

/-!
# A `levelSet` guard written with `atan2` is evaluated with the corner hull, and misses

`@levelSet/isIntersecting_.m` (`aux_isIntersecting_interval`) evaluates the level-set
function `ls.funHan` on `interval(S)` and reports no intersection for `'<='` when the infimum
of the result is positive. `funHan` is the `matlabFunction` of the user's equation, so a guard
`c - atan2(y, x) ≤ 0` calls `@interval/atan2.m` on the box. On `y ∈ [-1, 1]`, `x = -1` the
box contains the point `(x, y) = (-1, 0)` with `atan2 = π`, but the corner hull
`[-3π/4, 3π/4]` lies below some threshold `c ≤ π`, so the computed range of `c - atan2` is
positive and the guard is reported as not intersected (read from the source, not run). This
file states the interval part: the supremum of the corner hull is below a threshold `c` that
a point of the box reaches.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A threshold `c` with the corner hull's supremum below `c` and a point of the box with
`c ≤ atan2`: the guard `c - atan2 y x ≤ 0` holds at the point, yet CORA's range of `c - atan2`
has a positive infimum. -/
theorem Interval.atan2_cora_guard_missed :
    ∃ (I₁ I₂ : Interval (Vec ℝ 1)) (y x : Vec ℝ 1) (c : ℝ), y ∈ I₁.construct ∧ x ∈ I₂.construct ∧
      (I₁.atan2 I₂).sup 0 < c ∧ c ≤ Complex.arg ⟨x 0, y 0⟩ := by -- --- PROOF ---
  have hpi : Complex.arg ⟨-1, 0⟩ = Real.pi := by
    rw [Complex.arg_eq_pi_iff]; exact ⟨by norm_num, rfl⟩
  have h1 : Complex.arg ⟨-1, -1⟩ < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) fun e => by
      rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 (by norm_num)
  have h2 : Complex.arg ⟨-1, 1⟩ < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) fun e => by
      rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 (by norm_num)
  have hm := max_lt h1 h2
  -- threshold: midpoint between the hull's supremum and `π`
  refine ⟨⟨fun _ => -1, fun _ => 1⟩, ⟨fun _ => -1, fun _ => -1⟩, fun _ => 0, fun _ => -1,
    (max (Complex.arg ⟨-1, -1⟩) (Complex.arg ⟨-1, 1⟩) + Real.pi) / 2,
    fun i => ⟨by show (-1 : ℝ) ≤ 0; norm_num, by show (0 : ℝ) ≤ 1; norm_num⟩,
    fun i => ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
  · -- the hull supremum is the max of the four corner arguments, all below the threshold
    simp only [Interval.atan2]
    simp
    have a := le_max_left (Complex.arg ⟨-1, -1⟩) (Complex.arg ⟨-1, 1⟩)
    have b := le_max_right (Complex.arg ⟨-1, -1⟩) (Complex.arg ⟨-1, 1⟩)
    constructor <;> linarith
  · show _ ≤ Complex.arg ⟨-1, 0⟩
    rw [hpi]; linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
