import Probes.Round3PreparedOriginalParameterJointBeforeOrder
import Smoothing.Round3ParameterActualStageRawConsumer

/-! The original whole-parameter entrance internally constructs its reference
primary and secondary packets, one common C2 tolerance, the actual new normal,
and all canonical mean/secondary raw families. Geometry and tolerance precede
every order and budget. Each later stage returns one physical family and one
secondary choice at every observer and derivative order, without a supplied
prepared geometry, raw piece, mean estimate, or output estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round3_prepared_actual_original_coherent_before_order
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref hdRef hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hAll : Ref.parameterSet = univ)
    (hReference : ∀ p ∈ Ref.parameterOpen, ∀ x, Ref.reference p x ≠ 0)
    (hLinearRef : IncrementsOriginalLinearSmoothInputs Ref)
    (BS0 TS0 BP0 TP0 Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Ref.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i)
    (hFixed : ∀ j, parameterRound2_originalFixedPacketProfile Ref j 1 ≠ ⊤)
    (hFixedBound : ∀ j, (parameterRound2_originalFixedPacketProfile Ref j 1).toReal ≤ Given j) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
      (∀ j, 0 ≤ Tinv j) ∧ (∀ j, 0 ≤ Kcut j) ∧ (∀ j, 0 ≤ Tobs j) ∧
    ∀ (q : ℕ) (budget : ℝ), 0 ≤ budget →
    ∃ Cnormal : ℕ → ℝ, (∀ j, 0 ≤ Cnormal j) ∧
    ∀ reference : ℕ → ℝ,
    ∃ Cmap : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ, (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder q j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∀ (F : P × M → Ey)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius q budget reference Given)
      (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference Given stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ rho : ℝ, IncrementsOriginalDecompositionReserveInputs Data rho →
    Round3ParameterActualCoherentConclusion Ref hdRef hsRef hnRef theta packet profiles secondary F H neighborhood
      stage hF normal Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) ((Ds+1)*(Dp+1)) lower rho := by
  intro theta
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    round3_prepared_actual_original_parameter_joint_before_order Ref hdRef hsRef hpRef hnRef hImmRef lower hEllRef
      hF0joint hAll hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro q budget hbudget
  obtain ⟨Cnormal,hCnormal,hMake⟩ := hByOrder q budget hbudget
  refine ⟨Cnormal,hCnormal,?_⟩
  intro reference
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,hConsume⟩ :=
    round3Parameter_uniform_actual_stage_raw_consumer Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles
      secondary hSupport hPart ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) ((Ds+1)*(Dp+1)) hCount
      BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC Tinv Kcut Tobs
      hBS0 hTS0 hBP0 hTP0 hInverseC Ds Dp radius hradius q budget lower
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,?_⟩
  intro Packet F H neighborhood Data stage hd hs hDecomp S hF normal hFinite hBound rho hReserve
  obtain ⟨rebound,hActual,hImm,hPhase,hEll,stable,hRaw⟩ :=
    hMake F H neighborhood reference Given stage hd hs hDecomp hFinite hBound
  exact hConsume F H neighborhood stage normal hActual rebound stable hRaw hDecomp rho hReserve

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_original_coherent_before_order
