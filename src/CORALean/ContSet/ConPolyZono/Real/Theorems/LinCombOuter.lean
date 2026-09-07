import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesLinCombIff
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValue
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

/-!
# `linComb` contains every segment between the two constrained polynomial zonotopes

The witness is `PolyZonotope.linComb`'s — each set's own factors, `2λ-1` on the
fresh one, the zonotope pairing on the independent coefficients — and
`linComb_value` is the arithmetic, unchanged by the constraints.

What the constraints add is one goal: the combined system holds at that witness.
`satisfies_linComb_iff` splits it into the two operands' own systems at their own
factors, which the two segment endpoints already satisfy. So no nonemptiness
hypothesis: a point of `segments` hands over a point of *each* set, and with it
the witness that its constraints are satisfiable. That both systems are imposed
even at `λ = 0`, where the first operand's point drops out, costs nothing here.

Outer and not exact, for the reason `PolyZonotope.linComb_outer` is: the
independent block is enclosed by the pairing. The constraints give up nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.linComb_outer (cPZ₁ cPZ₂ : ConPolyZono α) :
    segments cPZ₁.construct cPZ₂.construct ⊆ (cPZ₁.linComb cPZ₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, ⟨a₁, β₁, ha₁, hβ₁, hs₁, rfl⟩, y₂, ⟨a₂, β₂, ha₂, hβ₂, hs₂, rfl⟩,
    lam, ⟨hl0, hl1⟩, rfl⟩
  have hA₁ : (fun k => Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)
      (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k))) = a₁ :=
    funext fun k => by rw [Fin.append_left, Fin.append_left]
  have hA₂ : (fun k => Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)
      (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) = a₂ :=
    funext fun k => by rw [Fin.append_left, Fin.append_right]
  refine ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1),
    Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam) (Zonotope.pairCoeffDiff β₁ β₂ lam),
    ?_, ?_, ?_, ?_⟩
  -- the fresh factor is `2λ-1`, which stays in `[-1,1]` for `λ` in the unit interval
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · refine Fin.addCases ?_ ?_
    · intro j
      simpa using Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro j
      simpa using Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
  -- the constraints: each endpoint satisfies its own, on the factors it came with
  · refine (ConPolyZono.satisfies_linComb_iff cPZ₁ cPZ₂ _).mpr ⟨?_, ?_⟩
    · rw [hA₁]
      exact hs₁
    · rw [hA₂]
      exact hs₂
  -- the value: the generators are `PolyZonotope.linComb`'s and so is the arithmetic
  · exact PolyZonotope.linComb_value cPZ₁.toPolyZonotope cPZ₂.toPolyZonotope a₁ β₁ a₂ β₂ lam

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
