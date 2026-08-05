/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Morphisms to `⦋1⦌`

**Local backport** of upstream Mathlib
`Mathlib/AlgebraicTopology/SimplexCategory/ToMkOne.lean`
(absent from the pinned Mathlib `v4.28.0`,
commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
The module-system syntax was removed, the `dsimp%` term-elaborator (absent here)
was replaced by the equivalent direct coercion `(toMk₁ i) j`, and a few `grind`
finishers that depend on a newer `grind` canonicalizer were replaced by
elementary `Fin`/`omega` arguments.

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → (⦋n⦌ ⟶ ⦋1⦌)`.
-/

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

/-- Given `i : Fin (n + 2)`, this is the morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex
category which corresponds to the monotone map `Fin (n + 1) → Fin 2` which
takes `i` times the value `0`. -/
def toMk₁ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs with h1 h2 h2
        · exact le_refl _
        · exact Fin.zero_le _
        · exact absurd (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr h) h2) h1
        · exact le_refl _ }

lemma toMk₁_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (toMk₁ i) j = if j.castSucc < i then 0 else 1 := rfl

lemma toMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (toMk₁ i) j = 0 ↔ j.castSucc < i := by
  grind +suggestions

lemma toMk₁_of_castSucc_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    (toMk₁ i) j = 0 := by
  -- By definition of `toMk₁`, we know that `(toMk₁ i) j = 0` if and only if `j.castSucc < i`.
  apply (toMk₁_apply_eq_zero_iff i j).mpr h

lemma toMk₁_apply_eq_one_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (toMk₁ i) j = 1 ↔ i ≤ j.castSucc := by
  constructor;
  · -- By definition of `toMk₁`, we know that `(toMk₁ i) j = 0` if and only if `j.castSucc < i`. Therefore, if `(toMk₁ i) j = 1`, then `j.castSucc ≥ i`.
    intro h
    by_contra h_contra
    push_neg at h_contra;
    exact absurd h ( by erw [ toMk₁_of_castSucc_lt _ _ h_contra ] ; decide );
  · exact fun h => if_neg ( not_lt_of_ge h )

lemma toMk₁_of_le_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    (toMk₁ i) j = 1 := by
  -- By definition of `toMk₁`, we know that `(toMk₁ i) j = 1` if and only if `i ≤ j.castSucc`.
  apply (toMk₁_apply_eq_one_iff i j).mpr h

lemma δ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    δ j ≫ toMk₁ i =
      toMk₁ (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  ext k;
  by_cases hk : k.val < i.val <;> simp_all +decide [ SimplexCategory.δ ];
  · simp +decide [ SimplexCategory.toMk₁, Fin.succAbove ];
    grind +suggestions;
  · simp +decide [ SimplexCategory.toMk₁, Fin.succAbove ];
    grind +suggestions

lemma δ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    δ j ≫ toMk₁ i = toMk₁ (i.pred (Fin.ne_zero_of_lt h)) := by
  obtain ⟨ i, rfl ⟩ := Fin.exists_succ_eq_of_ne_zero ( Fin.ne_zero_of_lt h );
  simp_all +decide [ SimplexCategory.toMk₁, SimplexCategory.δ ];
  ext k; simp [Fin.succAbove];
  grind +suggestions

lemma σ_comp_toMk₁_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    σ j ≫ toMk₁ i = toMk₁ i.castSucc := by
  -- By definition of σ j, we have σ j ≫ toMk₁ i = toMk₁ i.castSucc.
  ext k; simp [SimplexCategory.σ, SimplexCategory.toMk₁];
  split_ifs <;> simp_all +decide [ Fin.predAbove ]; all_goals grind +suggestions

lemma σ_comp_toMk₁_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    σ j ≫ toMk₁ i = toMk₁ i.succ := by
  ext k; exact (by
  simp +decide [ SimplexCategory.σ, SimplexCategory.toMk₁, Fin.predAbove ];
  grind +suggestions)

lemma toMk₁_injective {n : ℕ} : Function.Injective (toMk₁ (n := n)) := by
  intro i j hij;
  -- By choosing k = Fin.castSucc i, we can derive the inequality from the function equality.
  have h_ineq : ∀ k : Fin (n + 1), (toMk₁ i) k = (toMk₁ j) k → (k.castSucc < i ↔ k.castSucc < j) := by
    grind +suggestions;
  contrapose! h_ineq;
  cases lt_or_gt_of_ne h_ineq <;> [ refine' ⟨ ⟨ i, by omega ⟩, _, _ ⟩ ; refine' ⟨ ⟨ j, by omega ⟩, _, _ ⟩ ] <;> aesop

lemma toMk₁_surjective {n : ℕ} : Function.Surjective (toMk₁ (n := n)) := by
  -- To prove surjectivity, take any monotone function `f : ⦋n⦌ ⟶ ⦋1⦌` and find an `i : Fin (n + 2)` such that `toMk₁ i = f`.
  intro f
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 2), ∀ j : Fin (n + 1), f j = if j.castSucc < i then 0 else 1 := by
    by_cases h : ∃ j : Fin (n + 1), f j = 1;
    · obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), f j = 1 ∧ ∀ k : Fin (n + 1), k < j → f k = 0 := by
        exact ⟨ Finset.min' ( Finset.univ.filter fun j => f j = 1 ) ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.choose_spec ⟩ ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun j => f j = 1 ) ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.choose_spec ⟩ ⟩ ) |>.2, fun k hk => Or.resolve_right ( Fin.exists_fin_two.mp <| by aesop ) fun hk' => hk.not_ge <| Finset.min'_le _ _ <| by aesop ⟩;
      use Fin.castSucc j;
      intro k; split_ifs <;> simp_all +decide ;
      exact le_antisymm ( Fin.le_last _ ) ( hj.1 ▸ f.toOrderHom.monotone ‹_› );
    · use Fin.last _;
      intro j; specialize h; rcases Fin.exists_fin_two.mp ⟨ f j, rfl ⟩ with ha | ha <;> aesop;
  exact ⟨ i, by ext j; exact hi j ▸ rfl ⟩

lemma toMk₁_bijective {n : ℕ} : Function.Bijective (toMk₁ (n := n)) :=
  ⟨toMk₁_injective, toMk₁_surjective⟩

/-- The bijection `Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌)` which sends `i : Fin (n + 2)` to the
morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex category which corresponds to the monotone map
`Fin (n + 1) → Fin 2` which takes `i` times the value `0`. -/
@[simps! apply]
noncomputable def toMk₁Equiv {n : ℕ} : Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌) :=
  Equiv.ofBijective _ toMk₁_bijective

end SimplexCategory