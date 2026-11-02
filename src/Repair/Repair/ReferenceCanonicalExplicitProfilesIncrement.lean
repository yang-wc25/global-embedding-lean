import Repair.ReferenceCanonicalIncrement
import Repair.ReferenceCanonicalCompletedProfiles
import Probes.Round3RepairSecondaryEnlarge

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
attribute [local irreducible] incrementCanonical_round3ParameterMeanNormCost incrementCanonical_round3ParameterMeanSizeCost
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
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
local instance referenceCanonicalExplicitProfilesIncrementChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance referenceCanonicalExplicitProfilesIncrementIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- Explicit fixed maxima pay for both primary and secondary raw data.
The original prepared family is enlarged with the SAME choice; numerical
inequalities and T-profile bindings are not caller premises. -/
theorem referenceCanonical_round3_repair_explicit_profiles_increment
    (numbers : Round3RepairMeanPrimitiveProfiles) (Ctarget : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (Rsecondary : ℕ) (Mrest Kcut Tinv Tobs : ℕ → ℝ) :
    let Input := numbers.canonicalInputProfile.{uM,uP,0,0,uΒ} (Parameters := P) (Primaries := Fin Data.primaryCount) (Refinements := Β)
      (m := m) (d := d) (N := N) (Tr := ℝ)
      (fun j => Ctarget j*budget+(j+1)*packet.closedReferenceProfile j) q hq
    let profile := numbers.complete q Input Rsecondary Mrest Kcut Tinv Tobs
    ∀ (reserved : ReferenceCanonicalRepairReservedCosts (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget),
    reserved.generated.targetCost=Ctarget →
    ∀ (state : Round3RepairCurrentSmoothingState packet q budget)
    (witness : Round3RepairCanonicalMeanWitness (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet reserved.generated.cost (reserved.generated.data state))
    (normal : Fin Data.primaryCount → P × M → Ey) (domain : Fin Data.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace IT x) // A.IsSymm}),
    let E := round3ParameterStageData Data (state.smoothedMap packet) (state.computedTarget packet)
      Data.parameterOpen normal domain neighborhood
    let cost := reserved.generated.cost
    let mean := (witness.toRawMean packet).toMean packet
    ∀ (hd : IncrementsOriginalDomainConditions E)
      (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → Round3ParameterSecondaryChoice P M m)
      (hChoicePreserves : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
      (family : ∀ ip : Fin Data.parameterCount,
        Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) E
          (fun p x => state.smoothedMap packet ((Data.parameterChart ip).symm p,x))
          (fun p => (reserved.generated.data state).slice_smooth ((Data.parameterChart ip).symm p))
          (round3ParameterNativePrimary (fun p x => state.smoothedMap packet (p,x))
            (mean.restrictedPrimary packet) (Data.parameterChart ip)) q state.ell
          (round3ParameterNativeDomain (Data.parameterChart ip) (univ : Set (P × M)))
          (round3ParameterNativeDomain (Data.parameterChart ip) (univ : Set (P × M)))
          Mrest Kcut Tinv Tobs Rsecondary
          (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' packet.closedSamples (i.1,ip)))
      (hChoice : ∀ ip, (family ip).choice=round3ParameterNativeChoices choice (Data.parameterChart ip))
      (e delta : ℝ) (he : 0 < e) (heTheta : e < cost.Theta),
    ∃ out : Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β)
      (SubSecondary := SubSecondary) packet cost (reserved.generated.data state) e delta,
      out.mean=witness.toRawMean packet ∧ out.choice=choice := by
  intro Input profile reserved hTarget state witness normal domain neighborhood E cost mean hd choice
    hChoicePreserves family hChoice e delta he heTheta
  rcases reserved.generated.profiles with
    ⟨hRho,hReserve,hRsub,hLprimary,hRsecondary,hBnd,hMg,hDinput,hT,hBsec,hMsec,hCcut,hTsec,hTinv,hTobs⟩
  have hInput : reserved.iterateProfile packet profile hq=Input :=
    referenceCanonical_round3_repair_completed_iterate_profile packet numbers Ctarget hq Input Rsecondary Mrest Kcut Tinv Tobs reserved hTarget
  have hPayB (j) : cost.Bnd (actualSecondarySolveOrder q j)
      (reserved.iterateProfile packet profile hq (actualSecondarySolveOrder q j+(q+4))) ≤ cost.Bsec j := by
    rw [hBnd,hBsec,hInput]
    exact le_max_right _ _
  have hPayM (j) : cost.Mg (actualSecondarySolveOrder q j) ≤ cost.Msec j := by
    rw [hMg,hMsec]
    exact le_max_left _ _
  have hM (j) : Mrest j ≤ cost.Msec j := by rw [hMsec]; exact le_max_right _ _
  have hCut (j) : Kcut j ≤ cost.Ccut j := by rw [hCcut]; exact le_max_right _ _
  have hCount : Rsecondary ≤ cost.Rsecondary := by rw [hRsecondary]; exact le_rfl
  let family' := fun ip => (family ip).round3Repair_enlargeProfiles cost.Msec cost.Ccut
    (fun a => max 0 (Tinv a)) (fun a => max 0 (Tobs a)) cost.Rsecondary
    hM hCut (fun _ => le_max_right _ _) (fun _ => le_max_right _ _) hCount
  have hChoice' (ip) : (family' ip).choice=round3ParameterNativeChoices choice (Data.parameterChart ip) := hChoice ip
  apply referenceCanonical_round3_repair_canonical_increment_witness packet profile hq reserved state witness normal domain neighborhood
    hd (fun a => max 0 (Tinv a)) (fun a => max 0 (Tobs a)) hPayB hPayM
    (fun j => ?_) (fun j => ?_) (fun j => ?_) choice hChoicePreserves family' hChoice' e delta he heTheta
  · rw [hTsec,hT]
    rfl
  · rw [hTinv]
    rfl
  · rw [hTobs]
    rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.referenceCanonical_round3_repair_explicit_profiles_increment
