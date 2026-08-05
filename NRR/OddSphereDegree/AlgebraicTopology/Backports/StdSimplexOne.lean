/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import NRR.OddSphereDegree.AlgebraicTopology.Backports.SimplexCategoryToMkOne

/-!
# Simplices in `Δ[1]`

**Local backport** of upstream Mathlib
`Mathlib/AlgebraicTopology/SimplicialSet/StdSimplexOne.lean`
(absent from the pinned Mathlib `v4.28.0`).
The module-system syntax was removed and the `dsimp%` term-elaborator (absent
here) was avoided.

We define a bijection `SSet.stdSimplex.objMk₁` between `Fin (n + 2)` and
`Δ[1] _⦋n⦌` for any `n : ℕ`, and describe the action of faces and degeneracies.
-/

universe u

open CategoryTheory Simplicial

namespace SSet

namespace stdSimplex

/-- Given `i : Fin (n + 2)`, this is the `n`-simplex of `Δ[1]` which corresponds
to the monotone map `Fin (n + 1) → Fin 2` which takes `i` times the value `0`. -/
def objMk₁ {n : ℕ} (i : Fin (n + 2)) : (Δ[1] _⦋n⦌ : Type u) :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs with h1 h2 h2
        · exact le_refl _
        · exact Fin.zero_le _
        · exact absurd (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr h) h2) h1
        · exact le_refl _ }

lemma objEquiv_objMk₁ {n : ℕ} (i : Fin (n + 2)) :
    stdSimplex.objEquiv (objMk₁.{u} i) = SimplexCategory.toMk₁ i := rfl

lemma δ_objMk₁_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    Δ[1].δ j (objMk₁.{u} i) =
      objMk₁.{u} (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  apply stdSimplex.objEquiv.injective;
  convert SimplexCategory.δ_comp_toMk₁_of_le i j h using 1

lemma δ_objMk₁_of_lt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    Δ[1].δ j (objMk₁.{u} i) = objMk₁.{u} (i.pred (Fin.ne_zero_of_lt h)) := by
  convert SimplexCategory.δ_comp_toMk₁_of_lt i j h using 1;
  convert Iff.rfl using 2;
  constructor <;> intro h';
  · convert congr_arg ( fun f => stdSimplex.objEquiv.symm f ) h' using 1;
  · convert SimplexCategory.δ_comp_toMk₁_of_lt i j h using 1

lemma σ_objMk₁_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.castSucc := by
  convert SimplexCategory.σ_comp_toMk₁_of_le i j h using 1;
  constructor <;> intro h';
  · convert SimplexCategory.σ_comp_toMk₁_of_le i j h using 1;
  · convert congr_arg ( fun f => stdSimplex.objEquiv.symm f ) h' using 1

lemma σ_objMk₁_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.succ := by
  refine' stdSimplex.objEquiv.injective _;
  convert SimplexCategory.σ_comp_toMk₁_of_lt i j h using 1

lemma objMk₁_bijective {n : ℕ} : Function.Bijective (objMk₁.{u} (n := n)) :=
  ((SimplexCategory.toMk₁Equiv (n := n)).trans objEquiv.symm).bijective

lemma objMk₁_injective {n : ℕ} : Function.Injective (objMk₁.{u} (n := n)) :=
  objMk₁_bijective.injective

lemma objMk₁_surjective {n : ℕ} : Function.Surjective (objMk₁.{u} (n := n)) :=
  objMk₁_bijective.surjective

end stdSimplex

end SSet