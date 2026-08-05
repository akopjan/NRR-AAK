import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import NRR.BodySpace
import NRR.EMP.VariableBody
import NRR.Multivalued
import NRR.TestMap.EquivarianceCore

/-!
# Phase interfaces for the prime configuration model

This module collects the stable APIs established before the prime-equivariant layer.  It contains
no new mathematical assertion; later `PrimeModel` modules import this file rather than depending on
implementation details of the hyperspace, variable-body, or multivalued-function developments.
-/

namespace NRR

namespace PrimeModel

abbrev SiteFamily := EMP.VariableBody.SiteFamily

end PrimeModel

end NRR
