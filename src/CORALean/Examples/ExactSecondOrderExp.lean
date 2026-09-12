import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureContainsExact

/-!
# The second-order term of a box of matrices, exactly

`expIntervalW` is the one enclosure in the tree that is not merely sound: its
bounds are values `W(t)` really takes, which is what a `_attained` use site
looks like — an existential rather than a containment.

What that buys is the last `example` here: the sharper enclosure of
[1, Thm. 3.2] sits inside the uniform one of [1, Sec. 3.3.1] at every order
from two up, and no size of box or step can turn that round. Soundness alone
would not give it; only the bounds being attained does.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A full `±1` box, every entry uncertain and every entry independent of every
other — the case interval arithmetic is worst at and this is sharpest on. -/
noncomputable def ESO.A : Interval (Mat ℝ 2 2) := ⟨fun _ _ => (-1 : ℝ), fun _ _ => 1⟩

/-- Non-empty, which is what the witnesses of `expIntervalW_attained` need. -/
theorem ESO.le : ∀ p q, ESO.A.inf p q ≤ ESO.A.sup p q := fun _ _ => by norm_num [ESO.A]

/-- Every member's `W(t)` lands in the box [1, Lemma 3.1] computes. -/
example {M : Mat ℝ 2 2} (hM : M ∈ ESO.A.construct) :
    MatExp.expW M 1 ∈ (MatExp.expIntervalW ESO.A 1).construct :=
  MatExp.expW_mem_expIntervalW ESO.A 1 hM

/-- And each of its bounds is such a `W(t)`, so nothing narrower would do. -/
example (i j : Fin 2) :
    ∃ M ∈ ESO.A.construct, MatExp.expW M 1 i j = (MatExp.expIntervalW ESO.A 1).inf i j :=
  (MatExp.expIntervalW_attained ESO.A one_ne_zero ESO.le i j).1

/-- Which is why the exact-second-order enclosure never leaves the uniform one. -/
example (κ : ℕ) (hκ : 2 ≤ κ) :
    (MatExp.expIntervalEnclosureExact ESO.A 1 κ).construct
      ⊆ (MatExp.expIntervalEnclosure (Interval.smul 1 ESO.A) κ).construct :=
  MatExp.expIntervalEnclosure_contains_exact ESO.A one_ne_zero ESO.le hκ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
