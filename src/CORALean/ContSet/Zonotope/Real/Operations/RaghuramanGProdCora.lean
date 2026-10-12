import CORALean.ContSet.Zonotope.Real.Operations.SortByLength

/-!
# `Zonotope.raghuramanGProdCora`, CORA's `G_prod` in the `'raghuraman'` reduction

CORA's `@zonotope/reduceUnderApprox.m`, `aux_reduceUnderApproxRaghuraman` (lines 260-281), up to
`G_prod = G_small'*G_big` (line 270): `aux_selectSmallestGenerators` (lines 625-645) sorts the
generators by decreasing squared length and splits them into the `eta_new` largest (`G_big`) and
the rest (`G_small`). Entry `(k, i)` is the product of the `k`-th small with the `i`-th big
generator, both in sorted order.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `G_prod` for `eta_new = etaNew` (`etaNew ≤ Z.h`). -/
noncomputable def Zonotope.raghuramanGProdCora (Z : Zonotope (Vec ℝ n)) (etaNew : ℕ)
    (hr : etaNew ≤ Z.h) : Fin (Z.h - etaNew) → Fin etaNew → ℝ :=
  -- [c,G_big,G_small] = aux_selectSmallestGenerators(Z,eta_new,'length')   (line 266)
  let Zs := Z.sortByLength
  let G_big := fun i : Fin etaNew =>
    Zs.G ⟨i, by have := i.2; simp only [Zs, Zonotope.sortByLength]; omega⟩
  let G_small := fun k : Fin (Z.h - etaNew) =>
    Zs.G ⟨etaNew + k, by have := k.2; simp only [Zs, Zonotope.sortByLength]; omega⟩
  -- G_prod = G_small'*G_big                                                (line 270)
  fun k i => dotProduct (G_small k) (G_big i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
