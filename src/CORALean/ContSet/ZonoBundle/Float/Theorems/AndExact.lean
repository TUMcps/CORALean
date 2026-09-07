import CORALean.ContSet.ZonoBundle.Float.Operations.And

/-!
# `ZonoBundle.and` denotes exactly the intersection

Appending the two families intersects what each bundle denoted:
`Fin.forall_fin_add` splits membership in the appended family the same way
`Fin.append` splits the family itself. The members' error boxes ride along
inside their own `construct`, so the argument is the exact layer's unchanged —
this is the one operation here that loses nothing over floats either.

`Instances` is what turns it into the `And (ZonoBundle 𝕋 n) (Vec ℝ n)` instance,
whose obligation is only the outer half.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.and_exact (zB₁ zB₂ : ZonoBundle 𝕋 n) :
    (zB₁.and zB₂).construct = zB₁.construct ∩ zB₂.construct := by
  ext x
  simp only [ZonoBundle.construct, ZonoBundle.and, Set.mem_iInter, Set.mem_inter_iff,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
