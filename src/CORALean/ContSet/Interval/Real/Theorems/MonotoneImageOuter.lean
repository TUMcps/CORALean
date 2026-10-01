import CORALean.ContSet.Interval.Real.Interval

/-!
# A box contains the image under a monotone function

A strictly monotone function that is continuous on an interval `D` of the reals maps a box with
corners in `D` onto exactly the box of its endpoint images, by the intermediate value theorem
coordinate by coordinate. An antitone one swaps the two corners. Without continuity (`sign`,
`round`) only the outer statement holds: the image sits inside the box of endpoint images, with
no hypothesis on `f` beyond `Monotone`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone `f`, nothing else: the image lies in the box of endpoint images. -/
theorem Interval.monotoneImage_outer (f : ℝ → ℝ) (hf : Monotone f) (I : Interval (Vec ℝ n)) :
    (fun x i => f (x i)) '' I.construct
      ⊆ (⟨fun i => f (I.inf i), fun i => f (I.sup i)⟩ : Interval (Vec ℝ n)).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
  exact ⟨hf hx'.1, hf hx'.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
