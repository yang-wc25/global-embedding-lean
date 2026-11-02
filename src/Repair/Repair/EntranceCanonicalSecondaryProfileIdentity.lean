import Repair.EntranceCanonicalCompletedProfile
import Probes.Round4ParameterSecondaryGeometryProfile
import Probes.Round4ParameterStageInputFinite

/-!
# Complete numerical identity of the reference-generated repair profiles

This proposition records the exact finite-maximum secondary cost, the
shifted actual cutoff profile, and their actual mean/secondary completion.
It is consumed by the original-data repair theorem for the same trajectory.
The geometric scalar reserves and the reference transition profiles remain
explicit primitives; their uniform original-data construction is separate.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def RepairEntranceCanonicalSecondaryCompletedProfiles
    (radius : ℝ) (hradius : 0 < radius) (Ds Dp : ℕ)
    (BS TS BP TP Given reference metricReference : ℕ → ℝ)
    (budget : ℝ) (Lprimary : ℕ)
    (SubSecondary : Type uSubSecondary) [Fintype SubSecondary]
    (profile : ℕ → Round3RepairPrimitiveProfiles) (Ctarget : ℕ → ℕ → ℝ) : Prop :=
  ∃ Forward Inverse Meta Tinv Kcut Tobs : ℕ → ℝ,
  ∃ normalF normalT meanReserve c cT : ℝ,
  ∃ hMeanReserve : 0 < meanReserve,
  ∃ Rsub Rsecondary : ℕ,
  ∃ secondaryReserve : SubSecondary → ℝ,
  let Packet := fun r => round4ParameterStageInputProfile m d N radius hradius
    BS TS BP TP Inverse Forward Given reference Ds Dp (40*(10+r+1)) budget normalF normalT
  ∃ hPacket : ∀ r j, 0 ≤ Packet r j,
  ∀ r, profile r =
    repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,0,uΒ} (m := m) (d := d) (N := N)
      (fun j => Ctarget r j*budget+(j+1)*metricReference j)
      (40*(10+r+1)) Rsub Lprimary Rsecondary (by omega)
      meanReserve hMeanReserve c cT (Packet r) Forward Inverse Meta (hPacket r)
      (round4ParameterSecondaryGeometryProfile m d N (40*(10+r+1)) secondaryReserve
        (Packet r) Tinv Tobs c)
      (fun j => Kcut (actualSecondarySolveOrder (40*(10+r+1)) j)) Tinv Tobs

end GlobalEmbedding.Continuation
