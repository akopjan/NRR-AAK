import NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Nondegeneracy of affine barycentric subdivision simplices

Every affine simplex in an iterated barycentric subdivision of `Δⁿ` is nondegenerate.  The vertex
matrix of one subdivision step is a permutation matrix times a triangular prefix-average matrix;
its determinant is a nonzero permutation sign times `∏ k, (k+1)⁻¹`.  Iterated subdivision remains
nondegenerate by multiplication.
-/

namespace NRR
namespace AffineSubdivisionDeterminant

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

/-- Matrix whose columns are the vertices of one barycentric subdivision simplex. -/
noncomputable def stepVertexMatrix
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => prefixBarycenter n pi k r

/-- Lower triangular prefix-average matrix before permutation of coordinates. -/
noncomputable def prefixAverageMatrix (n : Nat) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => if r.1 ≤ k.1 then (k.1 + 1 : Real)⁻¹ else 0

/-
Factorization of a one-step vertex matrix.
-/
theorem stepVertexMatrix_eq
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    stepVertexMatrix n pi = Equiv.Perm.permMatrix Real pi.symm * prefixAverageMatrix n := by
  ext r k; simp +decide [ Matrix.mul_apply, Equiv.Perm.permMatrix ] ;
  convert prefixBarycenter_val_eq_stepVertices n pi k |> fun h => congr_fun h r using 1;
  unfold prefixAverageMatrix BarycentricSubdivisionDiameter.stepVertices; simp +decide [ BarycentricSubdivisionDiameter.stdVerts ] ;
  split_ifs <;> simp_all +decide [ Finset.sum_apply, Pi.single_apply ];
  · rw [ Finset.card_eq_one.mpr ] ; aesop;
    use pi.symm r; ext; aesop;
  · exact Or.inr fun x hx => by intro H; have := pi.injective ( by aesop : pi x = pi ( pi.symm r ) ) ; exact absurd this ( ne_of_lt ( lt_of_le_of_lt hx ‹_› ) ) ;

/-
Determinant of the prefix-average matrix.
-/
theorem det_prefixAverageMatrix (n : Nat) :
    Matrix.det (prefixAverageMatrix n) =
      ∏ k : Fin (n + 1), (k.1 + 1 : Real)⁻¹ := by
  rw [ Matrix.det_of_upperTriangular ] <;> norm_num;
  · unfold prefixAverageMatrix; aesop;
  · intro i j hij;
    exact if_neg hij.not_ge

/-
One barycentric subdivision simplex is nondegenerate.
-/
theorem det_stepVertexMatrix_ne_zero
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    Matrix.det (stepVertexMatrix n pi) ≠ 0 := by
  rw [ stepVertexMatrix_eq ];
  simp +decide [ Matrix.det_permutation, det_prefixAverageMatrix ];
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_add_one_ne_zero _

/-- Vertex matrix of an iterated affine subdivision simplex. -/
noncomputable def iterVertexMatrix
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => affineCompMap n N rho (stdSimplex.vertex (S := Real) k) r

@[simp] theorem iterVertexMatrix_zero
    (n : Nat) (rho : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    iterVertexMatrix n 0 rho = 1 := by
  ext r k
  simp [iterVertexMatrix, Matrix.one_apply, stdSimplex.vertex, Pi.single_apply]

/-
Appending one subdivision step multiplies vertex matrices.
-/
theorem iterVertexMatrix_succ
    (n N : Nat) (rho : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    iterVertexMatrix n (N + 1) rho =
      iterVertexMatrix n N (fun i => rho i.castSucc) *
        stepVertexMatrix n (rho (Fin.last N)) := by
  ext r k; simp [iterVertexMatrix, affineCompMap_succ];
  -- By definition of matrix multiplication and the properties of the affine composition map, we can expand the right-hand side.
  have h_expand : ∀ (x : Delta n), (affineCompMap n N (fun i => rho i.castSucc) (affineSubdivMap n (rho (Fin.last N)) x)).val r = ∑ j, (affineCompMap n N (fun i => rho i.castSucc) (stdSimplex.vertex j)).val r * (affineSubdivMap n (rho (Fin.last N)) x).val j := by
    intro x
    have h_expand : (affineCompMap n N (fun i => rho i.castSucc) (affineSubdivMap n (rho (Fin.last N)) x)).val = affineCompLinear n N (fun i => rho i.castSucc) (affineSubdivMap n (rho (Fin.last N)) x).val := by
      convert affineCompMap_coe n N ( fun i => rho i.castSucc ) ( affineSubdivMap n ( rho ( Fin.last N ) ) x ) using 1;
    have h_expand : ∀ (v : Fin (n + 1) → ℝ), affineCompLinear n N (fun i => rho i.castSucc) v = ∑ j, v j • affineCompLinear n N (fun i => rho i.castSucc) (Pi.single j 1) := by
      intro v; exact (by
      convert ( affineCompLinear n N ( fun i => rho i.castSucc ) ).pi_apply_eq_sum_univ v using 1;
      exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;);
    convert congr_fun ( h_expand ( affineSubdivMap n ( rho ( Fin.last N ) ) x |> Subtype.val ) ) r using 1;
    · exact congr_fun ‹_› r;
    · simp +decide [ mul_comm, Finset.sum_apply, Pi.single_apply ];
      congr! 2;
      convert congr_fun ( affineCompMap_coe n N ( fun i => rho i.castSucc ) ( stdSimplex.vertex _ ) ) r using 1;
  convert h_expand ( stdSimplex.vertex k ) using 1;
  simp +decide [ Matrix.mul_apply, iterVertexMatrix, stepVertexMatrix ];
  convert rfl;
  exact affineSubdivMap_vertex _ _ _

/-- Every iterated subdivision simplex is nondegenerate. -/
theorem det_iterVertexMatrix_ne_zero
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) :
    Matrix.det (iterVertexMatrix n N rho) ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [iterVertexMatrix_succ, Matrix.det_mul]
      exact mul_ne_zero (ih _) (det_stepVertexMatrix_ne_zero n _)

end AffineSubdivisionDeterminant
end NRR