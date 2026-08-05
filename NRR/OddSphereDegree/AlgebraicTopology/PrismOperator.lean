import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Analysis.Convex.StdSimplex
import NRR.OddSphereDegree.AlgebraicTopology.HomotopyToChainHomotopy

/-!
# Singular prism construction

Builds the cylinder associated to a continuous homotopy after applying the
singular simplicial-set functor. The endpoint identities connect this
construction to the algebraic simplicial-homotopy and chain-homotopy machinery
used by the singular-homology homotopy-invariance proof.
-/
open CategoryTheory Limits AlgebraicTopology Simplicial

namespace SphereOddDegree

/-- The unit interval as an object of `TopCat`. -/
noncomputable def unitI : TopCat.{0} := TopCat.of unitInterval

/-- The singular simplicial set functor preserves limits, being a right adjoint
(`sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet`). -/
noncomputable instance singularPreservesLimits : Limits.PreservesLimits TopCat.toSSet.{0} :=
  sSetTopAdj.rightAdjoint_preservesLimits

/-- The const-valued continuous map `X → I` at a point `t` of the interval. -/
noncomputable def constI (X : TopCat.{0}) (t : unitInterval) : X ⟶ unitI :=
  TopCat.ofHom (ContinuousMap.const _ t)

/-- The standard topological `1`-simplex, viewed (via
`stdSimplexHomeomorphUnitInterval`) as a continuous map into the interval. -/
noncomputable def edgeCM : C(stdSimplex ℝ (Fin (1 + 1)), unitI) :=
  ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The singular edge of the interval: the simplicial `1`-simplex of `Sing I`
classified by the homeomorphism `Δ¹_top ≃ₜ I`. -/
noncomputable def edge : Δ[1] ⟶ TopCat.toSSet.obj unitI :=
  SSet.yonedaEquiv.symm
    ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)

/-- The const-valued simplicial map onto the `j`-th vertex of `Δ[1]`. -/
noncomputable def vtx (Z : SSet.{0}) (j : Fin 2) : Z ⟶ Δ[1] where
  app m := fun _ => SSet.stdSimplex.const 1 j m
  naturality := by intro a b φ; funext x; rfl

/-- A `ContinuousMap.Homotopy` between `f.hom` and `g.hom`, repackaged as a
single morphism out of the categorical product `X ⨯ I`. On a point `p` it is
`H (snd p, fst p)`, i.e. `H` with its interval coordinate first. -/
noncomputable def homotopyMap {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) : X ⨯ unitI ⟶ Y :=
  TopCat.ofHom
    { toFun := fun p => H.toContinuousMap
        ((Limits.prod.snd (X := X) (Y := unitI)) p, (Limits.prod.fst (X := X) (Y := unitI)) p)
      continuous_toFun := by
        apply H.toContinuousMap.continuous.comp
        exact ((Limits.prod.snd (X := X) (Y := unitI)).hom.continuous).prodMk
          ((Limits.prod.fst (X := X) (Y := unitI)).hom.continuous) }

/-- The **singular cylinder map** of a homotopy `H`:
`Sing X × Δ[1] ⟶ Sing Y`, built from the singular edge of the interval, the
product-preservation isomorphism `Sing X × Sing I ≅ Sing (X × I)`, and `Sing H`. -/
noncomputable def cylinder {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    TopCat.toSSet.obj X ⨯ Δ[1] ⟶ TopCat.toSSet.obj Y :=
  Limits.prod.map (𝟙 (TopCat.toSSet.obj X)) edge ≫
    (PreservesLimitPair.iso TopCat.toSSet X unitI).inv ≫
    TopCat.toSSet.map (homotopyMap H)

/-- The `j`-th endpoint section `Sing X ⟶ Sing X × Δ[1]`. -/
noncomputable def sect (X : TopCat.{0}) (j : Fin 2) :
    TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj X ⨯ Δ[1] :=
  Limits.prod.lift (𝟙 (TopCat.toSSet.obj X)) (vtx (TopCat.toSSet.obj X) j)

/-- At interval coordinate `0`, the repackaged homotopy recovers `f`. -/
theorem homotopyMap_zero {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    Limits.prod.lift (𝟙 X) (constI X 0) ≫ homotopyMap H = f := by
  convert TopCat.hom_ext ( ContinuousMap.ext ?_ ) using 1;
  simp [prod.lift, constI];
  convert H.map_zero_left using 1;
  convert Iff.rfl;
  convert rfl;
  convert congr_arg ( fun x => H.toContinuousMap x ) _;
  exact Prod.ext ( by exact congr_arg ( fun f => f ‹_› ) ( show ( limit.lift ( pair X unitI ) ( BinaryFan.mk ( 𝟙 X ) ( TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 0 ) ) ) ) ≫ prod.snd = TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 0 ) from by exact limit.lift_π _ _ ) ) ( by exact congr_arg ( fun f => f ‹_› ) ( show ( limit.lift ( pair X unitI ) ( BinaryFan.mk ( 𝟙 X ) ( TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 0 ) ) ) ) ≫ prod.fst = 𝟙 X from by exact limit.lift_π _ _ ) )

/-- At interval coordinate `1`, the repackaged homotopy recovers `g`. -/
theorem homotopyMap_one {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    Limits.prod.lift (𝟙 X) (constI X 1) ≫ homotopyMap H = g := by
  ext x;
  convert H.map_one_left x using 1;
  convert congr_arg ( fun x => H.toContinuousMap x ) _;
  exact Prod.ext ( by exact congr_arg ( fun f => f x ) ( show ( limit.lift ( pair X unitI ) ( BinaryFan.mk ( 𝟙 X ) ( TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 1 ) ) ) ) ≫ prod.snd = TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 1 ) from by exact limit.lift_π _ _ ) ) ( by exact congr_arg ( fun f => f x ) ( show ( limit.lift ( pair X unitI ) ( BinaryFan.mk ( 𝟙 X ) ( TopCat.ofHom ( ContinuousMap.const ( X : Type _ ) 1 ) ) ) ) ≫ prod.fst = 𝟙 X from by exact limit.lift_π _ _ ) )

/-- The `0`-vertex of `Δ[1]`, pushed along the singular edge, is the const-valued
singular map at `0 ∈ I`. -/
theorem edge_vtx_zero (X : TopCat.{0}) :
    vtx (TopCat.toSSet.obj X) 0 ≫ edge = TopCat.toSSet.map (constI X 0) := by
  ext m;
  simp +decide [ edge, vtx ];
  simp +decide [ SSet.yonedaEquiv, unitI, constI, edgeCM ];
  simp +decide [ uliftYonedaEquiv, SSet.stdSimplex.const ];
  simp +decide [ TopCat.toSSetObjEquiv, SSet.stdSimplex.objMk ];
  simp +decide [ TopCat.toSSet, SSet.stdSimplex.objEquiv, Equiv.ulift, ConcreteCategory.homEquiv ];
  congr! 1;
  ext; simp +decide [ stdSimplexHomeomorphUnitInterval ];
  simp +decide [ TopCat.uliftFunctor, stdSimplexEquivIcc ];
  simp +decide [ Homeomorph.ulift ];
  simp +decide [ ULift.map, stdSimplex.map ];
  simp +decide [ FunOnFinite.linearMap ];
  simp +decide [ Finsupp.mapDomain ];
  simp +decide [ ConcreteCategory.hom ]

/-- The `1`-vertex of `Δ[1]`, pushed along the singular edge, is the const-valued
singular map at `1 ∈ I`. -/
theorem edge_vtx_one (X : TopCat.{0}) :
    vtx (TopCat.toSSet.obj X) 1 ≫ edge = TopCat.toSSet.map (constI X 1) := by
  ext m x; simp +decide [ edge, vtx ] ;
  simp +decide [ SSet.yonedaEquiv, SSet.stdSimplex.const, unitI, constI, edgeCM ];
  simp +decide [ uliftYonedaEquiv, SSet.stdSimplex.objMk, TopCat.toSSet, TopCat.toSSetObjEquiv, Equiv.ulift, ConcreteCategory.homEquiv ];
  congr! 1;
  ext; simp +decide [ TopCat.uliftFunctor, stdSimplexHomeomorphUnitInterval ];
  simp +decide [ Homeomorph.ulift, ULift.map, stdSimplex.map ];
  simp +decide [ FunOnFinite.linearMap ];
  simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite ];
  simp +decide [ Finsupp.sum_fintype, Finsupp.single_apply ];
  simp +decide [ SSet.stdSimplex.objEquiv, SimplexCategory.Hom.mk, OrderHom.const ];
  simp +decide [ Equiv.ulift, ConcreteCategory.hom ];
  simp +decide [ SimplexCategory.Hom.toOrderHom ]

/-- Key reduction: the product-comparison inverse turns the lifted const-valued
section into `Sing` of the lifted topological section. -/
theorem lift_const_comp_iso_inv (X : TopCat.{0}) (j : unitInterval) :
    Limits.prod.lift (𝟙 (TopCat.toSSet.obj X)) (TopCat.toSSet.map (constI X j)) ≫
        (PreservesLimitPair.iso TopCat.toSSet X unitI).inv
      = TopCat.toSSet.map (Limits.prod.lift (𝟙 X) (constI X j)) := by
  rw [Iso.comp_inv_eq, PreservesLimitPair.iso_hom]
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp,
      Limits.prod.lift_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp,
      Limits.prod.lift_snd]

/-- **Endpoint identity (start).** The singular cylinder restricts to `Sing f`
along the start inclusion. -/
theorem cylinder_sect_zero {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    sect X 0 ≫ cylinder H = TopCat.toSSet.map f := by
  unfold cylinder sect;
  convert congr_arg ( fun x => x ≫ TopCat.toSSet.map ( homotopyMap H ) ) ( lift_const_comp_iso_inv X 0 ) using 1;
  · simp +decide [ ← Category.assoc, ← edge_vtx_zero ];
  · rw [ ← Functor.map_comp, homotopyMap_zero ]

/-- **Endpoint identity (end).** The singular cylinder restricts to `Sing g`
along the end inclusion. -/
theorem cylinder_sect_one {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    sect X 1 ≫ cylinder H = TopCat.toSSet.map g := by
  unfold sect cylinder; simp +decide [ ← Category.assoc ] ;
  convert congr_arg ( fun x => x ≫ TopCat.toSSet.map ( homotopyMap H ) ) ( lift_const_comp_iso_inv X 1 ) using 1;
  · rw [ edge_vtx_one ];
  · rw [ ← Functor.map_comp, homotopyMap_one ]

end SphereOddDegree