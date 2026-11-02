import Repair.IncrementActualSignedRefinement
import Repair.IncrementSecondaryReferenceBudget
import Probes.Round3PreparedParameterSecondaryTransport
import Repair.IncrementSecondaryChartBudget

/-! Actual nonlinear secondary charts, cutoffs and the complete physical
packet are selected together. All reference reserves and chart profiles
are the same named numerical budgets, chosen before current maps or jets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

variable [T2Space M]
theorem increment_actual_secondary_geometry
    (mu Mb R buffer coordinateBound kernel lower C2 : ℝ) (Phase : ℕ → ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hFirstBudget : Phase 1 ≤ Mb) (hSecondBudget : buffer*Phase 2 ≤ Mb)
    (hKernel : 0 < kernel) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ Ref.atlas.inner i.1)
    (region : ∀ r i, IncrementActualSignedRegion Ref i r
      ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
      mu R buffer coordinateBound kernel Phase)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (Bp Bs : ℝ) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hParameterValue : ∀ ip z, z ∈ Ref.parameterNormDomain ip → ‖z‖ ≤ Bp)
    (hSourceValue : ∀ ih z, z ∈ Ref.sourceNormDomain ih → ‖z‖ ≤ Bs) :
    ∃ (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
      (numeric : IncrementSecondaryReferenceBudget Ref hd hs theta packet)
      (charts : IncrementSecondaryChartBudget Ref hd hs theta packet),
      let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
      let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
      let B := 1+Forward 1
      numeric.nativeInverse = Inverse ∧
      numeric.cF = lower/B^2 ∧
      numeric.cT = (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      numeric.MH = actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      charts.forwardProfile = repairEntranceOriginalForwardProfile Bp Forward Parameter Spatial ∧
      charts.inverseProfile = repairEntranceOriginalInverseProfile Bp Bs Inverse Parameter Spatial ∧
      (∀ BS TS BP TP Ds Dp, charts.cutoffProfile BS TS BP TP Ds Dp =
        incrementSecondaryCutoffProfile (Ep × D) mu Mb buffer BS TS BP TP Ds Dp) ∧
      (∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2) ∧
      (∀ r i, (packet.s r i).card ≤ incrementScalarTotalRefinementBound («Ep» := Ep) (m := m)
        mu Mb R buffer coordinateBound Phase hmu hMb hbuffer hCoordinate hPhase hFirstBudget hSecondBudget) := by
  obtain ⟨packet,numeric,hInv,hFirst,hTrans,hHess,hCard,hNumbers,hCut,hSamples,hParam⟩ :=
    increment_actual_parameter_secondary_numerical_packet mu Mb R buffer coordinateBound kernel lower C2 Phase
      hmu hMb hbuffer hCoordinate hPhase hFirstBudget hSecondBudget hKernel hLower hC2
      Ref hd hs hAll hFjoint hEll hMapFinite hMap theta hCompact hSmooth hSupport region
  let charts : IncrementSecondaryChartBudget Ref hd hs theta packet := {
    mu := mu
    Mb := Mb
    buffer := buffer
    mu_pos := hmu
    Mb_nonneg := hMb
    buffer_pos := hbuffer
    nativeForward := incrementScalarForwardProfile Mb coordinateBound Phase
    nativeInverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
    parameterTransition := Parameter
    sourceTransition := Spatial
    nativeForward_nonneg := incrementScalarForwardProfile_nonneg Mb coordinateBound Phase hMb hCoordinate hPhase
    nativeInverse_nonneg := incrementScalarInverseProfile_nonneg mu Mb coordinateBound Phase hmu hMb hCoordinate hPhase
    parameterTransition_nonneg := hParameter
    sourceTransition_nonneg := hSpatial
    transition := transition
    forward := by
      intro r i a j z hz
      have h := (packet.piece r i a).forward_jets j z hz
      rwa [(hNumbers r i a).1] at h
    inverse := by
      intro r i a j z hz
      have h := (packet.piece r i a).inverse_jets j z hz
      rwa [(hNumbers r i a).2.1] at h
    samples := hSamples
    parameterValue := Bp
    sourceValue := Bs
    parameterValue_nonneg := hBp
    sourceValue_nonneg := hBs
    parameter_value := hParameterValue
    source_value := hSourceValue
    literal := fun r i a => (hNumbers r i a).2.2
    scalar := fun r i j a x => hCut r i j buffer hbuffer.le le_rfl a x }
  exact ⟨packet,numeric,charts,hInv,hFirst,hTrans,hHess,rfl,rfl,
    fun _ _ _ _ _ _ => rfl,hParam,hCard⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_secondary_geometry
