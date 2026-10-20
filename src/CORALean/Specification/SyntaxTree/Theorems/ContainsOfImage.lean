module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The image of a point lies in the image of its interval

An interval op that is exact for a function `f` (`J.construct = f '' I.construct`) holds `f t`
wherever `I`
holds `t`, one coordinate: what the forward value of a node needs.

## Inputs
* `I` – interval
* `J` – image interval
* `f` – function
* `t` – point

## Hypotheses
* `h` – the second interval is the image of the first
* `ht` – the point lies in the first interval

## Conclusion
* the function value lies in the image interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- If `J` is the image of `I` under `f`, it holds `f t` where `I` holds `t`. -/
theorem SyntaxTree.contains_of_image {I J : Dom} {f : ℝ → ℝ}
    (h : J.construct = (fun x i => f (x i)) '' I.construct) {t : ℝ}
    (ht : Dom.contains I t) : Dom.contains J (f t) := by -- --- PROOF ---
  have hx : (fun _ => t : Vec ℝ 1) ∈ I.construct := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact ht
  have hmem : (fun i => f ((fun _ => t : Vec ℝ 1) i) : Vec ℝ 1) ∈ J.construct := by
    rw [h]; exact ⟨_, hx, rfl⟩
  have := hmem 0
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
