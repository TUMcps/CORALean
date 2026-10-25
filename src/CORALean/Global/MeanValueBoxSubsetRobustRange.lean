module

public import CORALean.Global.RobustUnderApproxBox
public import CORALean.Global.RobustRangeVec

@[expose] public section

/-!
# The product of the mean-value AE extensions is inside the robust range

[1, Remark 1]: `Thm. 3` with the disturbance inputs `I_A` outside the domain of `π`, so that they
are universal in every component, gives an under-approximation of the robust range. The paper
writes `π : {1, …, m} → ({1, …, n} \ I_A)`, whose codomain takes the input set `I_A` out of the set
of components; it is read as `π` defined on the inputs `{1, …, m} \ I_A`, as "the disturbance part
of the input components will always be quantified universally" says. Here `π : Fin m → Fin n` is
only used off `IA`. The hypotheses are those of `Thm. 3`
([`UnderApproxRangeBox.lean`](UnderApproxRangeBox.lean)), with the inputs `j ∈ IA` in no `π⁻¹(i)`.

## Inputs
* `f` – function from inputs to components
* `IA` – disturbance inputs
* `π` – assignment of control inputs to components
* `lo` – lower corner of the input box
* `hi` – upper corner of the input box
* `f0lo` – lower bounds on the center values
* `f0hi` – upper bounds on the center values
* `dwhi` – upper bounds on the partials in the disturbance inputs
* `dulo` – lower bounds on the partials in the control inputs

## Hypotheses
* `hlh` – the input box is nonempty
* `hf` – every component is continuously differentiable
* `hf0` – the center values lie within their bounds
* `hw` – the disturbance partials are bounded above on the path sets
* `hu` – the control partials are bounded below

## Conclusion
* the product of the inner intervals lies in the robust range

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to Reachability of
      Non-Linear Control Systems With Disturbances". IEEE Control Systems Letters, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Remark 1]: the product of the inner intervals of `Thm. 2` of the components, with the
inputs `IA` universal in all of them, is inside the robust range. -/
theorem meanValueBox_subset_robustRangeVec {f : (Fin m → ℝ) → Fin n → ℝ} {IA : Finset (Fin m)}
    {π : Fin m → Fin n} {lo hi : Fin m → ℝ} (hlh : lo ≤ hi)
    (hf : ∀ i, ContDiff ℝ 1 fun x => f x i) {f0lo f0hi : Fin n → ℝ}
    (hf0 : ∀ i, f (fun j => (lo j + hi j) / 2) i ∈ Icc (f0lo i) (f0hi i))
    (dwhi dulo : Fin n → Fin m → ℝ)
    (hw : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, j ∉ IA → π j = i → y j = (lo j + hi j) / 2) →
      ∀ j, j ∈ IA ∨ π j ≠ i → |fderiv ℝ (fun x => f x i) y (Pi.single j 1)| ≤ dwhi i j)
    (hu : ∀ i, ∀ y ∈ Icc lo hi, ∀ j, j ∉ IA → π j = i →
      dulo i j ≤ |fderiv ℝ (fun x => f x i) y (Pi.single j 1)|) : -- --- CONCL ---
    Icc (fun i => f0hi i - ∑ j with (j ∉ IA ∧ π j = i), dulo i j * ((hi j - lo j) / 2)
        + ∑ j with (j ∈ IA ∨ π j ≠ i), dwhi i j * ((hi j - lo j) / 2))
      (fun i => f0lo i + ∑ j with (j ∉ IA ∧ π j = i), dulo i j * ((hi j - lo j) / 2)
        - ∑ j with (j ∈ IA ∨ π j ≠ i), dwhi i j * ((hi j - lo j) / 2))
      ⊆ robustRangeVec f IA lo hi := by -- --- PROOF ---
  classical
  intro z hz w hw'
  -- the partial map `π` as an `Option`, `none` on the disturbances
  have key : ∀ j i, (if j ∈ IA then none else some (π j) : Option (Fin n)) = some i
      ↔ (j ∉ IA ∧ π j = i) := fun j i => by by_cases h : j ∈ IA <;> simp [h]
  have key' : ∀ j i, ¬ ((if j ∈ IA then none else some (π j) : Option (Fin n)) = some i)
      ↔ (j ∈ IA ∨ π j ≠ i) := fun j i => by
    rw [key]; tauto
  -- and the index sets of the sums in both readings
  have e1 : ∀ i, (Finset.univ.filter fun j => (if j ∈ IA then none else some (π j) :
      Option (Fin n)) = some i) = Finset.univ.filter fun j => j ∉ IA ∧ π j = i :=
    fun i => Finset.filter_congr fun j _ => key j i
  have e2 : ∀ i, (Finset.univ.filter fun j => ¬ ((if j ∈ IA then none else some (π j) :
      Option (Fin n)) = some i)) = Finset.univ.filter fun j => j ∈ IA ∨ π j ≠ i :=
    fun i => Finset.filter_congr fun j _ => key' j i
  obtain ⟨x, hx, hxA, hfx⟩ := exists_eq_of_mean_value_box
    (π := fun j => if j ∈ IA then none else some (π j)) hlh hf hf0 dwhi dulo
    (fun i y hy hyE j hj => hw i y hy (fun j' h1 h2 => hyE j' ((key j' i).mpr ⟨h1, h2⟩)) j
      ((key' j i).mp hj)) (fun i y hy j hj => hu i y hy j ((key j i).mp hj).1 ((key j i).mp hj).2)
    (z := z) (w := w) (by
      simp only [e1, e2]
      exact hz) hw'
  exact ⟨x, hx, fun j hj => hxA j (by simp [hj]), hfx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
