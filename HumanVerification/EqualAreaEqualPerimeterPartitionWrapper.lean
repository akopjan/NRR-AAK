import HumanVerification.Transfer
import HumanVerification.CauchyCrofton.Theorem

open Set MeasureTheory

noncomputable section

namespace HumanVerification

/--
Internal generic wrapper.  Its conclusion is definitionally equal to the
human-facing statement once `Main.lean` supplies the model instance locally inside the proof of its
public theorem.
-/
theorem equalAreaEqualPerimeterPartitionWrapper
    {α : Type} [NRR.HumanExport.ConvexFigureModel α]
    (F : α) (n : ℕ) (hn : 0 < n) :
    ∃ pieces : Fin n → α,
      NRR.HumanExport.IsConvexPartition F pieces ∧
      (∀ i j,
        NRR.HumanExport.area (pieces i) =
          NRR.HumanExport.area (pieces j)) ∧
      (∀ i j,
        NRR.HumanExport.perimeter (pieces i) =
          NRR.HumanExport.perimeter (pieces j)) := by
  exact NRR.HumanExport.equalAreaEqualPerimeterPartition_of_cauchyCrofton
    CauchyCrofton.cauchyCroftonStatement F n hn

end HumanVerification
