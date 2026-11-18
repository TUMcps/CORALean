module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyGirardReduceFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyBoxOutFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonoGenSetAppend

@[expose] public section

/-!
# `LinearSys.verifyGirardReduceFloat` encloses what it was given

A point spanned by the old generators, plus one spanned by the new ones, plus a point of the box,
is a point spanned by the generators that stay plus a point of the new box: both moves into the box
(the axis-aligned new generators, then the reduced ones) are `LinearSys.verifyBoxOutFloat`, whatever
the metric and the budget chose.

## Inputs
* `P` – float generators so far
* `new` – float new generators
* `b` – float radius of the box
* `budget` – float budget of the reduction
* `y₁` – point spanned by the old generators
* `y₂` – point spanned by the new generators
* `e` – point of the box

## Hypotheses
* `h₁` – `y₁` is spanned by `P`
* `h₂` – `y₂` is spanned by `new`
* `he` – `e` lies in the box

## Conclusion
* `y₁ + y₂ + e` is spanned by the generators that stay plus a point of the new box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.mem_verifyGirardReduceFloat (P new : List (Vec 𝕋 n)) (b : Vec 𝕋 n)
    (budget : 𝕋) {y₁ y₂ e : Vec ℝ n} (h₁ : y₁ ∈ LinearSys.verifyZonoGenSet (P.map toRealVec))
    (h₂ : y₂ ∈ LinearSys.verifyZonoGenSet (new.map toRealVec))
    (he : ∀ i, |e i| ≤ toReal (b i)) : -- --- CONCL ---
    ∃ y' ∈ LinearSys.verifyZonoGenSet
        ((LinearSys.verifyGirardReduceFloat P new b budget).1.map toRealVec),
      ∃ e' : Vec ℝ n,
        (∀ i, |e' i| ≤ toReal ((LinearSys.verifyGirardReduceFloat P new b budget).2 i)) ∧
        y₁ + y₂ + e = y' + e' := by -- --- PROOF ---
  unfold LinearSys.verifyGirardReduceFloat
  dsimp only
  -- the axis-aligned new generators into the box
  set La := new.map fun g => (g, !le (LinearSys.step_verifyGirardFloat g) zero) with hLa
  have hLa1 : (La.map Prod.fst).map toRealVec = new.map toRealVec := by
    rw [hLa, List.map_map, List.map_map]; rfl
  obtain ⟨y₂', hy₂', e₁, he₁, h2⟩ :=
    LinearSys.mem_verifyBoxOutFloat La b (by rw [hLa1]; exact h₂) he
  -- the rest with the old ones, then the reduction
  set P₁ := P ++ (LinearSys.verifyBoxOutFloat La b).1 with hP₁
  have hy : y₁ + y₂' ∈ LinearSys.verifyZonoGenSet (P₁.map toRealVec) := by
    rw [hP₁, List.map_append]; exact LinearSys.add_mem_verifyZonoGenSet_append h₁ hy₂'
  set gir := P₁.map LinearSys.step_verifyGirardFloat
  set order := (List.range P₁.length).mergeSort fun i j => le (gir.getD i zero) (gir.getD j zero)
  set out := order.take (LinearSys.step_verifyGirardCountFloat budget
    (order.filterMap fun i => P₁[i]?) (fun _ => zero) 0)
  set Lr := P₁.zipIdx.map fun g => (g.1, !out.contains g.2) with hLr
  have hLr1 : (Lr.map Prod.fst).map toRealVec = P₁.map toRealVec := by
    rw [hLr, List.map_map, List.map_map]
    have : ((toRealVec ∘ Prod.fst) ∘ fun g : Vec 𝕋 n × ℕ => (g.1, !out.contains g.2))
        = toRealVec ∘ Prod.fst := rfl
    rw [this, ← List.map_map, List.zipIdx_map_fst]
  obtain ⟨y', hy', e', he', h3⟩ :=
    LinearSys.mem_verifyBoxOutFloat Lr (LinearSys.verifyBoxOutFloat La b).2
      (by rw [hLr1]; exact hy) he₁
  exact ⟨y', hy', e', he', by rw [add_assoc, h2, ← add_assoc, h3]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
