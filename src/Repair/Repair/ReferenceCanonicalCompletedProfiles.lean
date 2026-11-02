import Repair.ReferenceCanonicalMeanProfile
import Smoothing.Round3RepairPrimitiveProfileFactory

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
attribute [local irreducible] incrementCanonical_round3ParameterMeanNormCost incrementCanonical_round3ParameterMeanSizeCost
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance referenceCanonicalCompletedProfilesChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance referenceCanonicalCompletedProfilesIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The explicit Kq input profile is computed from the fixed mean
constants and the actual SH constant, before any secondary maximum is taken. -/
def Round3RepairMeanPrimitiveProfiles.canonicalInputProfile
    {Parameters : Type uP} {Primaries : Type uΛ} {Refinements : Type uΒ}
    (mean : Round3RepairMeanPrimitiveProfiles) (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) : ℕ → ℝ :=
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
    q mean.Rsub mean.Lprimary hq mean.reserve mean.reserve_pos mean.Bnd mean.Mg
      mean.Bnd_nonneg mean.Mg_nonneg mean.T mean.T_nonneg
  parameterRound2_uniformMeanProfile B0 Csize (q+4) q

/-- Completing the secondary constants does not change the mean iteration
or its numerical input profile. The same actual target constant is bound
explicitly to the reserved-cost factory output. -/
theorem referenceCanonical_round3_repair_completed_iterate_profile
    (mean : Round3RepairMeanPrimitiveProfiles) (Ctarget : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) {budget : ℝ} (Input : ℕ → ℝ)
    (Rsecondary : ℕ) (Mrest Kcut Tinv Tobs : ℕ → ℝ)
    (reserved : ReferenceCanonicalRepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet (mean.complete q Input Rsecondary Mrest Kcut Tinv Tobs) q hq budget)
    (hTarget : reserved.generated.targetCost=Ctarget) :
    reserved.iterateProfile packet (mean.complete q Input Rsecondary Mrest Kcut Tinv Tobs) hq =
      mean.canonicalInputProfile.{uM,uP,uTr,uΛ,uΒ} (Parameters := P) (Primaries := Λ) (Refinements := Β)
        (m := m) (d := d) (N := N) (Tr := Tr)
        (fun j => Ctarget j*budget+(j+1)*packet.closedReferenceProfile j) q hq := by
  unfold ReferenceCanonicalRepairReservedCosts.iterateProfile Round3RepairMeanPrimitiveProfiles.canonicalInputProfile
  simp only [Round3RepairMeanPrimitiveProfiles.complete, hTarget]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.referenceCanonical_round3_repair_completed_iterate_profile
