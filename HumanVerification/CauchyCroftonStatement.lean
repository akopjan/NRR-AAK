import HumanVerification.InternalModel

open Set MeasureTheory

noncomputable section

namespace HumanVerification

/-- The exact general planar Cauchy--Crofton bridge needed by the wrapper. -/
def CauchyCroftonStatement : Prop :=
  ∀ K : NRR.Geometry.ConvexBody NRR.HumanExport.Plane,
    (μH[1] : Measure NRR.HumanExport.Plane)
        (frontier (K : Set NRR.HumanExport.Plane)) =
      ENNReal.ofReal (NRR.Geometry.ConvexBody.perimeter K)

end HumanVerification
