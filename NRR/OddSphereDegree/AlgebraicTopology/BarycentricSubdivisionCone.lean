import NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import Mathlib
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# The cone operator for the barycentric subdivision homotopy

This file defines the affine **cone over a point** construction at the level of
the topological standard simplices, bundles it as a continuous map, extends it to
singular chains of `Δⁿ`, and proves the boundary identity

```text
∂ Cone_v(c) = c - Cone_v(∂ c)
```

in the exact degree-indexed form needed for the recursive proof that barycentric
subdivision is chain-homotopic to the identity.

For a point `v : Δⁿ` and a (continuous) `k`-simplex `τ : Δᵏ → Δⁿ`, the cone
`Cone_v(τ) : Δᵏ⁺¹ → Δⁿ` sends the new apex vertex to `v` and the remaining
vertices to the vertices of `τ`. In barycentric coordinates, writing
`x = (t, x₁, …, x_{k+1})` for a point of `Δᵏ⁺¹`,

```text
Cone_v(τ)(x) = t · v + (1 - t) · τ( x₁/(1-t), …, x_{k+1}/(1-t) )
```

away from `t = 1`, and `= v` at `t = 1` (the apex).

This file does **not** assert the barycentric subdivision homotopy itself; it only
builds the cone operator and its boundary formula.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. The normalized tail of a point of `Δᵏ⁺¹` -/

/-- The (un-normalized) coordinate function of the normalized tail of a point
`x : Δᵏ⁺¹`: the `i`-th coordinate is `x_{i+1} / (1 - x₀)`. (Lean's `/0 = 0`
convention makes this total; the genuine simplex point is `coneTail` below.) -/
noncomputable def coneTailFun {k : ℕ} (x : Delta (k + 1)) : Fin (k + 1) → ℝ :=
  fun i => (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0)

/-
When `x₀ ≠ 1`, the normalized tail coordinates form a genuine point of `Δᵏ`.
-/
theorem coneTailFun_mem {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTailFun x ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine' ⟨ fun i => _, _ ⟩;
  · exact div_nonneg ( x.2.1 _ ) ( sub_nonneg.2 ( x.2.2 ▸ Finset.single_le_sum ( fun a _ => x.2.1 a ) ( Finset.mem_univ 0 ) ) );
  · have h_sum : ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 - (x : Fin (k + 1 + 1) → ℝ) 0 := by
      exact eq_sub_of_add_eq' ( by simpa [ Fin.sum_univ_succ ] using x.2.2 );
    unfold coneTailFun;
    rw [ ← Finset.sum_div, h_sum, div_self ( sub_ne_zero_of_ne <| Ne.symm hx ) ]

/-- The normalized tail of `x : Δᵏ⁺¹`, as a point of `Δᵏ`. Away from the apex
(`x₀ = 1`) it is the genuine normalized tail; at the apex it is given an
irrelevant fallback value. -/
noncomputable def coneTail {k : ℕ} (x : Delta (k + 1)) : Delta k :=
  if h : (x : Fin (k + 1 + 1) → ℝ) 0 = 1 then stdSimplex.vertex (0 : Fin (k + 1))
  else ⟨coneTailFun x, coneTailFun_mem x h⟩

/-
Coordinate formula for `coneTail` away from the apex.
-/
theorem coneTail_apply {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) (i : Fin (k + 1)) :
    (coneTail x : Fin (k + 1) → ℝ) i
      = (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0) := by
  unfold coneTail; aesop;

/-! ## 2. The affine cone map -/

/-- The coordinate function of the cone of `τ` over `v` at the point `x`. -/
noncomputable def affineConeMapFun {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : Fin (n + 1) → ℝ :=
  fun j => (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
      + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j

/-
The cone coordinate function always defines a point of `Δⁿ`.
-/
theorem affineConeMapFun_mem {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : affineConeMapFun v τ x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine' ⟨ fun j => _, _ ⟩;
  · exact add_nonneg ( mul_nonneg ( stdSimplex.zero_le x 0 ) ( stdSimplex.zero_le v j ) ) ( mul_nonneg ( sub_nonneg.mpr ( stdSimplex.le_one x 0 ) ) ( stdSimplex.zero_le ( τ ( coneTail x ) ) j ) );
  · unfold affineConeMapFun;
    simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, stdSimplex.sum_eq_one ]

/-- **The affine cone map** `Cone_v(τ) : Δᵏ⁺¹ → Δⁿ`. -/
noncomputable def affineConeMap {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    Delta (k + 1) → Delta n :=
  fun x => ⟨affineConeMapFun v τ x, affineConeMapFun_mem v τ x⟩

@[simp] theorem affineConeMap_coord {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) (j : Fin (n + 1)) :
    (affineConeMap v τ x : Fin (n + 1) → ℝ) j
      = (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
        + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j := rfl

/-! ## 3. Vertex formulas -/

/-
The cone sends the apex vertex `0` to `v`.
-/
theorem affineConeMap_vertex_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    affineConeMap v τ (stdSimplex.vertex (0 : Fin (k + 1 + 1))) = v := by
  unfold affineConeMap; simp +decide [ stdSimplex.vertex ] ;
  unfold affineConeMapFun; simp +decide [ Fin.ext_iff, Pi.single_apply ] ;
  rfl

/-
The cone sends the vertex `i+1` to the vertex `τ(i)` of `τ`.
-/
theorem affineConeMap_vertex_succ {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (i : Fin (k + 1)) :
    affineConeMap v τ (stdSimplex.vertex i.succ) = τ (stdSimplex.vertex i) := by
  ext j;
  rw [ affineConeMap_coord ] ; simp +decide [ Fin.succ_ne_zero ];
  congr;
  ext j; simp +decide [ coneTail_apply, stdSimplex.vertex ] ;
  simp +decide [ Pi.single_apply, Fin.ext_iff ]

/-! ## 4. Continuity and the bundled continuous cone map -/

/-
`coneTail` is continuous away from the apex.
-/
theorem continuousOn_coneTail {k : ℕ} :
    ContinuousOn (coneTail (k := k)) {x : Delta (k + 1) | (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1} := by
  -- Write `S := {x : Delta (k+1) | (x:_) 0 ≠ 1}`.
  set S : Set (Delta (k + 1)) := {x | x 0 ≠ 1};
  have h_cont_tail : ContinuousOn (fun x : Delta (k + 1) => (coneTail x : Fin (k + 1) → ℝ)) S := by
    refine' ContinuousOn.congr _ _;
    exact fun x i => ( x : Fin ( k + 1 + 1 ) → ℝ ) i.succ / ( 1 - ( x : Fin ( k + 1 + 1 ) → ℝ ) 0 );
    · exact continuousOn_pi.mpr fun i => ContinuousOn.div ( continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) ( continuousOn_const.sub <| continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) fun x hx => sub_ne_zero_of_ne <| Ne.symm hx;
    · intro x hx; ext i; exact coneTail_apply x hx i;
  rw [ continuousOn_iff_continuous_restrict ] at *;
  exact continuous_induced_rng.mpr h_cont_tail

/-
The cone of a continuous `τ` over `v` is continuous.
-/
theorem continuous_affineConeMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    Continuous (affineConeMap v (⇑τ)) := by
  refine' continuous_induced_rng.mpr _;
  refine' continuous_pi fun j => _;
  -- The function $B(x) = (1 - x 0) * ((τ (coneTail x)) j)$ is continuous because it is a product of continuous functions.
  have hB_cont : Continuous (fun x : Delta (k + 1) => (1 - x 0) * ((τ (coneTail x)) j)) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    by_cases hx : x 0 = 1;
    · refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      refine' squeeze_zero ( fun _ => norm_nonneg _ ) ( fun e => _ ) ( Continuous.tendsto' ( show Continuous fun e : Delta ( k + 1 ) => |1 - e 0| from Continuous.abs <| continuous_const.sub <| continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) _ _ <| by aesop );
      simp +decide [ hx ];
      exact mul_le_of_le_one_right ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ stdSimplex.zero_le ( τ ( coneTail e ) ) j ], by linarith [ stdSimplex.le_one ( τ ( coneTail e ) ) j ] ⟩ );
    · refine' ContinuousAt.mul _ _;
      · exact ContinuousAt.sub continuousAt_const ( continuousAt_subtype_val.comp continuousAt_id |> ContinuousAt.comp ( continuousAt_apply _ _ ) );
      · refine' ContinuousAt.comp ( continuous_apply j |> Continuous.continuousAt ) _;
        refine' ContinuousAt.comp _ _;
        · exact Continuous.continuousAt ( by continuity );
        · refine' ContinuousAt.comp _ _;
          · exact τ.continuous.continuousAt;
          · exact continuousOn_coneTail.continuousAt ( IsOpen.mem_nhds ( isOpen_compl_singleton.preimage ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ) hx );
  convert Continuous.add ( Continuous.mul ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) continuous_const ) hB_cont using 1

/-- **The bundled continuous cone map** `Cone_v(τ) : C(Δᵏ⁺¹, Δⁿ)`. -/
noncomputable def affineConeContinuousMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    C(Delta (k + 1), Delta n) :=
  ⟨affineConeMap v (⇑τ), continuous_affineConeMap v τ⟩

@[simp] theorem affineConeContinuousMap_apply {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n))
    (x : Delta (k + 1)) : affineConeContinuousMap v τ x = affineConeMap v (⇑τ) x := rfl

/-! ## 5. Face formulas -/

/-
**Face opposite the apex.** Restricting the cone along the `0`-th coface
recovers the base simplex `τ`.
-/
theorem cone_face_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    (fun y : Delta k => affineConeMap v τ (cofaceTop k 0 y)) = τ := by
  ext y j;
  rw [ affineConeMap_coord ];
  rw [ show ( cofaceTop k 0 ) y = stdSimplex.map ( S := ℝ ) ( Fin.succAbove 0 ) y from rfl ];
  rw [ show coneTail ( stdSimplex.map ( Fin.succAbove 0 ) y ) = y from _ ];
  · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
  · ext i;
    convert coneTail_apply _ _ i using 1;
    · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
      rw [ Finset.sum_eq_single i ] <;> aesop;
    · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ]

/-
**Tail commutes with internal cofaces.** For `y` away from the apex, the
normalized tail of `cofaceTop (k+1) (j+1) y` is the `j`-th coface of the
normalized tail of `y`.
-/
theorem coneTail_cofaceTop_succ {k : ℕ} (j : Fin (k + 1 + 1)) (y : Delta (k + 1))
    (hy : (y : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTail (cofaceTop (k + 1) j.succ y) = cofaceTop k j (coneTail y) := by
  unfold cofaceTop;
  ext i; simp +decide [ coneTail_apply, Fin.succ_succAbove_succ, Fin.succ_succAbove_zero ] ;
  by_cases h : ( stdSimplex.map j.succ.succAbove y : Fin ( k + 1 + 1 + 1 ) → ℝ ) 0 = 1 <;> simp_all +decide [ coneTail_apply, Fin.succ_succAbove_succ, Fin.succ_succAbove_zero ];
  · simp_all +decide [ FunOnFinite.linearMap_apply_apply ];
    rw [ Finset.sum_eq_single 0 ] at h <;> simp_all +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
  · simp +decide [ FunOnFinite.linearMap_apply_apply, coneTail_apply y hy ] at *;
    rw [ ← Finset.sum_div _ _ _, show ( Finset.filter ( fun x => j.succ.succAbove x = 0 ) Finset.univ : Finset ( Fin ( k + 1 + 1 ) ) ) = { 0 } from ?_, show ( Finset.filter ( fun x => j.succ.succAbove x = i.succ ) Finset.univ : Finset ( Fin ( k + 1 + 1 ) ) ) = Finset.image ( fun x => x.succ ) ( Finset.filter ( fun x => j.succAbove x = i ) Finset.univ ) from ?_ ] <;> norm_num;
    · ext x; simp +decide [ Fin.succ_succAbove_succ ] ;
      cases x using Fin.inductionOn <;> simp +decide [ Fin.succ_succAbove_succ ];
      exact ne_of_lt ( Fin.succ_pos _ );
    · grind +suggestions

/-
**Every other face.** Restricting the cone along the `(j+1)`-th coface gives
the cone over the `j`-th face of `τ`.
-/
theorem cone_face_succ {n k : ℕ} (v : Delta n) (τ : Delta (k + 1) → Delta n)
    (j : Fin (k + 1 + 1)) :
    (fun y : Delta (k + 1) => affineConeMap v τ (cofaceTop (k + 1) j.succ y))
      = (fun y : Delta (k + 1) => affineConeMap v (fun z : Delta k => τ (cofaceTop k j z)) y) := by
  funext y;
  ext c;
  by_cases hy : ( y : Fin ( k + 1 + 1 ) → ℝ ) 0 = 1 <;> simp_all +decide [ affineConeMap_coord, cofaceTop_eq ];
  · simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ];
    rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
  · rw [ show ( cofaceTop ( k + 1 ) j.succ ) y 0 = y 0 from ?_, coneTail_cofaceTop_succ j y hy ];
    unfold cofaceTop; simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ] ;
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;

/-! ## 6. The cone on singular simplices and chains of `Δⁿ` -/

/-- The cone of a singular `k`-simplex of `Δⁿ` over `v`, as a singular
`(k+1)`-simplex of `Δⁿ`. -/
noncomputable def coneSimplex (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplices (TopCat.of (Delta n)) (k + 1) :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) (k + 1)
    (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ))

/-- The continuous map underlying `coneSimplex`. -/
theorem coneSimplex_continuousMap (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)
      = affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) := by
  rw [coneSimplex, singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
    Equiv.apply_symm_apply]

/-- The `0`-simplex with value `v` at every vertex. -/
noncomputable def constSimplex0 (n : ℕ) (v : Delta n) :
    singularSimplices (TopCat.of (Delta n)) 0 :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) 0
    (ContinuousMap.const (Delta 0) v)

/-
**Apex face of `coneSimplex`.** The `0`-th boundary face of the cone of `σ`
is `σ`.
-/
theorem coneSimplex_face_zero (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k 0 (coneSimplex n k v σ) = σ := by
  have h_cont : (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)).comp (cofaceTop k 0) = singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ := by
    ext y;
    convert congr_fun ( cone_face_zero v ( fun y => singularSimplexAsContinuousMap ( TopCat.of ( Delta n ) ) k σ y ) ) y |> congr_arg ( fun f => f ‹_› ) using 1;
  apply singularSimplices_ext;
  convert h_cont using 1

/-
**Internal faces of `coneSimplex`.** The `(j+1)`-th boundary face of the cone
of `σ` is the cone of the `j`-th boundary face of `σ`.
-/
theorem coneSimplex_face_succ (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (k + 1)) (j : Fin (k + 1 + 1)) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (k + 1) j.succ (coneSimplex n (k + 1) v σ)
      = coneSimplex n k v (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k j σ) := by
  apply singularSimplices_ext; simp [faceSimplex_continuousMap, coneSimplex_continuousMap];
  ext y; simp [affineConeContinuousMap_apply, ContinuousMap.comp_apply];
  convert congr_arg ( fun f => f ‹_› ) ( congrFun ( cone_face_succ v ( singularSimplexAsContinuousMap { carrier := ↑(Delta n), str := instTopologicalSpaceSubtype } (k + 1) σ ) j ) y ) using 1

/-
**The second face of a 1-dimensional cone.** The `1`-st boundary face of the
cone of a `0`-simplex `σ` is the simplex with value `v` at every vertex.
-/
theorem coneSimplex_face_one_zero (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) 0 1 (coneSimplex n 0 v σ)
      = constSimplex0 n v := by
  apply singularSimplices_ext;
  rw [ faceSimplex_continuousMap, coneSimplex_continuousMap ];
  ext y; simp [affineConeContinuousMap_apply, affineConeMap_coord];
  simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
  simp +decide [ Finset.filter_singleton, Fin.succAbove ];
  unfold singularSimplexAsContinuousMap constSimplex0; aesop;

/-! ## 7. The cone on chains -/

/-- The cone of a basis generator `[σ]`. -/
noncomputable def coneGenerator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  chainGenerator R (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)

/-- The `R`-linear map `R → C_{k+1}(Δⁿ; R)` sending `1` to `coneGenerator … σ`. -/
noncomputable def coneGeneratorHom (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  ModuleCat.ofHom
    { toFun := fun r => r • coneGenerator R n k v σ
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro a r; simp [mul_smul] }

/-- **The cone operator on chains** `Cone_v : C_k(Δⁿ; R) → C_{k+1}(Δⁿ; R)`. -/
noncomputable def coneLinearMap (R : Type) [CommRing R] (n k : ℕ) (v : Delta n) :
    singularChainGroup R (TopCat.of (Delta n)) k
      ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  Sigma.desc fun σ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v σ

/-
The cone operator has the prescribed value on a basis generator.
-/
theorem coneLinearMap_generator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = coneGenerator R n k v σ := by
  convert one_smul _ _;
  convert congr_arg ( fun f : ModuleCat.of R R ⟶ singularChainGroup R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( k + 1 ) => f.hom 1 ) ( Sigma.ι_desc ( fun σ => coneGeneratorHom R n k v σ ) σ ) using 1

/-! ## 8. The boundary formula -/

/-
**Boundary of the cone (base degree).** In degree `0`,
`∂ Cone_v([σ]) = [σ] - [const_v]`.
-/
theorem singularBoundary_coneGenerator_zero (R : Type) [CommRing R] (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    (singularBoundary R (TopCat.of (Delta n)) 0).hom (coneGenerator R n 0 v σ)
      = chainGenerator R (TopCat.of (Delta n)) 0 σ
        - chainGenerator R (TopCat.of (Delta n)) 0 (constSimplex0 n v) := by
  convert singularBoundary_chainGenerator_formula R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } 0 ( coneSimplex n 0 v σ ) using 1;
  rw [ Fin.sum_univ_two ] ; norm_num [ sub_eq_add_neg ];
  rw [ coneSimplex_face_zero, coneSimplex_face_one_zero ]

/-
**Boundary of the cone (successor degree).** For `σ` of degree `m+1`,
`∂ Cone_v([σ]) = [σ] - Cone_v(∂[σ])`.
-/
theorem singularBoundary_coneGenerator_succ (R : Type) [CommRing R] (n m : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (m + 1)) :
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
        - (coneLinearMap R n m v).hom
            ((singularBoundary R (TopCat.of (Delta n)) m).hom
              (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := by
  convert singularBoundary_chainGenerator_formula R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( m + 1 ) ( coneSimplex n ( m + 1 ) v σ ) using 1;
  rw [ Fin.sum_univ_succ ];
  simp +decide [ singularBoundary_chainGenerator_formula, coneSimplex_face_zero, coneSimplex_face_succ, coneLinearMap_generator ];
  simp +decide [ pow_succ', neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg ];
  rfl

/-
**The cone chain-homotopy identity (successor degree).**
`∂ ∘ Cone + Cone ∘ ∂ = id` on `C_{m+1}(Δⁿ; R)`.
-/
theorem singularBoundary_coneLinearMap (R : Type) [CommRing R] (n m : ℕ) (v : Delta n) :
    coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v
      = 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1)) := by
  apply Sigma.hom_ext;
  intro σ; ext; simp +decide [ ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.add_apply ] ;
  convert congr_arg ( fun x => x + ( coneLinearMap R n m v ).hom ( ( singularBoundary R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } m ).hom ( chainGenerator R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( m + 1 ) σ ) ) ) ( singularBoundary_coneGenerator_succ R n m v σ ) using 1 ; ring!;
  · convert rfl;
    convert coneLinearMap_generator R n ( m + 1 ) v σ |> Eq.symm;
  · simp +decide [ chainGenerator ];
    rfl

end AffineBarycentricSubdivision
end SphereOddDegree