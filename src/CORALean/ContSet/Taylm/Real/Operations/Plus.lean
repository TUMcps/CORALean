import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.plus`

CORA's `plus` of two models over the same variables: the term lists side by side and the
remainders added. CORA merges equal monomials afterwards (`priv_compress`); that changes
the list, not the polynomial, and is not done here. Not the Minkowski sum of the two range
sets: the variables are shared, which is why this is no `Plus` instance.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.plus (T₁ T₂ : Taylm n) : Taylm n :=
  ⟨T₁.terms ++ T₂.terms, T₁.remInf + T₂.remInf, T₁.remSup + T₂.remSup,
    max T₁.maxOrder T₂.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
