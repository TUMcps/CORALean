import CORALean.ContSet.Zonotope.Float.Operations.Split
/-!
# `Zonotope.splitFirstGen`, over a floating-point scalar

CORA's `@zonotope/splitFirstGen`: `h(j) = norm(G(:,j)'*G, 1)`, `[~,index] = max(h)` and
`split(Z, index)`. The scores are `sumUp` of `absolute` of `dotUp`, and the index is a left fold
over the generator indices that keeps the running best unless a later score is not known to be
`≤` it, so a tie keeps the first. `le` has no order laws, so this is a ranking; `split_outer`
holds at every index, so a misranking costs precision alone. A zonotope with no generator is its
own two halves.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along the generator of maximal `‖g_jᵀ G‖₁`. -/
def Zonotope.splitFirstGen (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n × Zonotope 𝕋 n :=
  let h := fun j => sumUp fun k => absolute (dotUp (fun i => Z.G i j) (fun i => Z.G i k))
  let index := (List.finRange Z.h).foldl
    (fun best j => match best with
      | none => some j
      | some b => if le (h j) (h b) then some b else some j)
    none
  match index with
  | some j => Z.split j
  | none => (Z, Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
