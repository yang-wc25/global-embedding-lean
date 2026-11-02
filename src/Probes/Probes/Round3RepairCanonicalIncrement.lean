import Probes.Round3RepairCanonicalMean
import Probes.Round3RepairMeanProfile
import Probes.Round3ParameterCanonicalRawAtlas
import Probes.Round3ParameterFixedProfileRebase

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairCanonicalIncrementChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairCanonicalIncrementIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The actual canonical primary mean and one coherent physical
secondary family construct the complete repair witness at the same Kq.
Its reserve and every input budget are proved internally before the final
raw atlas is built, so no secondary estimate is used circularly. -/
theorem round3_repair_canonical_increment_witness
    (profile : Round3RepairPrimitiveProfiles) {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (reserved : Round3RepairReservedCosts (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget)
    (state : Round3RepairCurrentSmoothingState packet q budget)
    (witness : Round3RepairCanonicalMeanWitness (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet reserved.generated.cost (reserved.generated.data state))
    (normal : Fin Data.primaryCount → P × M → Ey) (domain : Fin Data.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace IT x) // A.IsSymm}) :
    let E := round3ParameterStageData Data (state.smoothedMap packet) (state.computedTarget packet)
      Data.parameterOpen normal domain neighborhood
    let cost := reserved.generated.cost
    let mean := (witness.toRawMean packet).toMean packet
    let Input := reserved.iterateProfile packet profile hq
    ∀ (hd : IncrementsOriginalDomainConditions E)
      (Tinv Tobs : ℕ → ℝ)
      (hBsec : ∀ j, cost.Bnd (actualSecondarySolveOrder q j)
        (Input (actualSecondarySolveOrder q j+(q+4))) ≤ cost.Bsec j)
      (hMsec : ∀ j, cost.Mg (actualSecondarySolveOrder q j) ≤ cost.Msec j)
      (hT : ∀ j, cost.Tsec j=cost.T)
      (hTi : ∀ j, cost.Tinv j=Tinv) (hTo : ∀ j, cost.Tobs j=Tobs)
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
          cost.Msec cost.Ccut Tinv Tobs cost.Rsecondary
          (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' packet.closedSamples (i.1,ip)))
      (hChoice : ∀ ip, (family ip).choice=round3ParameterNativeChoices choice (Data.parameterChart ip))
      (e delta : ℝ) (he : 0 < e) (heTheta : e < cost.Theta),
    ∃ out : Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Data.primaryCount) (Β := Β)
      (SubSecondary := SubSecondary) packet cost (reserved.generated.data state) e delta,
      out.mean=witness.toRawMean packet ∧ out.choice=choice := by
  intro E cost mean Input hd Tinv Tobs hBsec hMsec hT hTi hTo choice hChoicePreserves family hChoice e delta he heTheta
  let D : IncrementsOriginalNativeData (m+1) d N M P := {E with parameterChart := packet.parameterFamily.chart}
  have hdD : IncrementsOriginalDomainConditions D := by
    have hE : D=E := by simp only [D,packet.chart_eq]; rfl
    exact hE.symm ▸ hd
  have hFamily : ∀ B : Fin Data.parameterCount → OpenPartialHomeomorph P Ep,
      B=Data.parameterChart →
      ∃ f : ∀ ip : Fin Data.parameterCount,
        Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) {E with parameterChart := B}
          (fun p x => state.smoothedMap packet ((B ip).symm p,x))
          (fun p => (reserved.generated.data state).slice_smooth ((B ip).symm p))
          (round3ParameterNativePrimary (fun p x => state.smoothedMap packet (p,x))
            (mean.restrictedPrimary packet) (B ip)) q state.ell
          (round3ParameterNativeDomain (B ip) (univ : Set (P × M)))
          (round3ParameterNativeDomain (B ip) (univ : Set (P × M)))
          cost.Msec cost.Ccut Tinv Tobs cost.Rsecondary
          (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' packet.closedSamples (i.1,ip)),
        ∀ ip, (f ip).choice=round3ParameterNativeChoices choice (B ip) := by
    intro B hB
    subst B
    exact ⟨family,hChoice⟩
  obtain ⟨f,hf⟩ := hFamily packet.parameterFamily.chart packet.chart_eq
  have hReserve := (round3_repair_generated_mean_iterate_reserve packet profile hq reserved state
    (witness.toRawMean packet) e he heTheta).2
  have hProfile := round3_repair_generated_mean_iterate_profile packet profile hq reserved state
    (witness.toRawMean packet) e he heTheta
  have hRaw := round3Parameter_canonical_all_order_raw_atlas D hdD
    (fun p x => state.smoothedMap packet (p,x)) (reserved.generated.data state).slice_smooth witness.g
    q cost.Rsub cost.Lprimary cost.Rsecondary state.ell cost.rho cost.reserve
    packet.closedSamples (Round3RepairPrimitiveMeanData.seminorm packet state.ell) mean.H
    cost.Bnd cost.Mg cost.Dinput cost.T witness.primary witness.canonical
    Input cost.Bsec cost.Msec cost.Ccut Tinv Tobs hBsec hMsec choice f hf
    (mean.iterate packet e) hReserve hProfile e delta he (heTheta.le.trans cost.theta_le_one)
  refine ⟨{ mean := witness.toRawMean packet
            choice := choice
            choice_preserves := hChoicePreserves
            raw := ?_ },rfl,rfl⟩
  intro j
  rw [hT j,hTi j,hTo j]
  exact hRaw j

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_canonical_increment_witness
