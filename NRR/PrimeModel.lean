import NRR.PrimeModel.PhaseInterfaces
import NRR.PrimeModel.ZeroSumAlgebra
import NRR.PrimeModel.CoordinateDecomposition
import NRR.PrimeModel.PrimeSymmetry
import NRR.PrimeModel.Actions
import NRR.PrimeModel.FixedVectors
import NRR.PrimeModel.EquivariantMap
import NRR.PrimeModel.Model
import NRR.PrimeModel.ModelSites
import NRR.PrimeModel.ChildEquivariance
import NRR.PrimeModel.ChildTestMap
import NRR.PrimeModel.BoundaryOrthants
import NRR.PrimeModel.AugmentedReference

/-!
# Prime configuration-model interface

This public aggregator exposes the algebraic and equivariant layer used by the prime-refinement
argument: the prime symmetry subgroup, zero-sum coordinate decomposition, abstract compact
configuration models, equivariant power-diagram children, child-evaluation test maps, endpoint
orthants, and the bounded augmented reference map.

It does not assert existence of the concrete polyhedral model and does not contain a PL
transversality, orbit-count, or separation theorem.
-/
