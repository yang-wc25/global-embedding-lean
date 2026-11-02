import Repair.IncrementActualSignedRefinement
import Repair.IncrementSecondaryReferenceBudget
import Probes.Round3PreparedParameterSecondaryTransport

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
theorem increment_actual_parameter_secondary_numerical_packet
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
      mu R buffer coordinateBound kernel Phase) :
    ∃ (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
      (numeric : IncrementSecondaryReferenceBudget Ref hd hs theta packet),
      let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
      let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
      let B := 1+Forward 1
      let radius := buffer/actualPhaseRefinementFactor mu Mb
      numeric.nativeInverse = Inverse ∧
      numeric.cF = lower/B^2 ∧
      numeric.cT = (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      numeric.MH = actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      (∀ r i, (packet.s r i).card ≤ incrementScalarTotalRefinementBound («Ep» := Ep) (m := m)
        mu Mb R buffer coordinateBound Phase hmu hMb hbuffer hCoordinate hPhase hFirstBudget hSecondBudget) ∧
      (∀ r i a, (packet.piece r i a).Forward = Forward ∧ (packet.piece r i a).Tinv = Inverse ∧
        (packet.piece r i a).cutoff = actualHostRefinementCutoff
          (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1))
          (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
          (actualRefinementCutoff (Ep × D) (packet.s r i) radius a.val)) ∧
      (∀ r i j (weight : ℝ), 0 ≤ weight → weight ≤ buffer → ∀ (a : packet.s r i) (x : Ep × D),
        weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff (Ep × D) (packet.s r i) radius a.val) x‖ ≤
          (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost (Ep × D) j) ∧
      (∀ r i a z, z ∈ (packet.piece r i a).native.source → parameterTensorModelEquiv (m+1) d z ∈
        incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
          Ref.parameterNormDomain Ref.parameterSet i) ∧
      (∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2) := by
  have hOpen (p : P) : p ∈ Ref.parameterOpen := hd.parameter_subset (by rw [hAll]; exact mem_univ _)
  let W := fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => (Ref.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW (i : Fin Ref.atlas.count × Fin Ref.parameterCount) : IsOpen (W i) := (Ref.parameterChart i.2).open_target.prod isOpen_univ
  have hSupport' (i : Fin Ref.atlas.count × Fin Ref.parameterCount) : tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSupport i hz).1,mem_univ _⟩
  have hNative (i : Fin Ref.atlas.count × Fin Ref.parameterCount) := round3Parameter_native_compact_parent (Ref.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) (hSupport' i)
  have hNSupport (i : Fin Ref.atlas.count × Fin Ref.parameterCount) : tsupport (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i)) ⊆
      W i ∩ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    have hh := hSupport i hz
    exact ⟨⟨(Ref.parameterChart i.2).map_source hh.1,mem_univ _⟩,
      mem_univ _,Ref.atlas.inner_subset i.1 hh.2⟩
  have hInner (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (y : Ep × M)
      (hy : y ∈ tsupport (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))) :
      y.2 ∈ Ref.atlas.inner i.1 := by
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact (hSupport i hz).2
  have hLocal (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :=
    increment_actual_original_signed_numerical_refinement mu Mb R buffer coordinateBound kernel lower C2 Phase
      hmu hMb hbuffer hCoordinate hPhase hFirstBudget hSecondBudget hKernel hLower hC2
      Ref hd hs hAll hFjoint hEll hMapFinite hMap i r (W i) (hW i)
      (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i) (region r i)
  choose s piece hCard hPart hParent hCount hNumbers hCut hSamples using hLocal
  have hLift (r : ActualSecondarySignedRecord (Fin Ref.primaryCount))
      (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (a : s r i) :=
    round3_prepared_parameter_secondary_cutoff_geometry Ref hd hs i r (W i)
      (piece r i a) (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent r i a)
  let packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta := {
    s := s
    piece := piece
    native_parent := hParent
    smooth := fun r i a => (hLift r i a).1
    compact := fun r i a => (hLift r i a).2.1
    parent := fun r i a => (hLift r i a).2.2
    source := fun r i a => (round3_prepared_parameter_secondary_carrier_source Ref hd hs i r
      (piece r i a) (theta i) (hSupport' i) (hLift r i a).2.2).1
    partition := fun r i z hz => round3_prepared_parameter_secondary_partition_transport Ref hd hs i r
      (piece r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2) (hPart r i) z hz
    count := fun r i z => round3_prepared_parameter_secondary_count_transport Ref hd hs i r
      (piece r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2)
      (5^Module.finrank ℝ (Ep × D)) (hCount r i) z }

  let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
  let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
  let B := 1+Forward 1
  have hF := incrementScalarForwardProfile_nonneg Mb coordinateBound Phase hMb hCoordinate hPhase
  have hI := incrementScalarInverseProfile_nonneg mu Mb coordinateBound Phase hmu hMb hCoordinate hPhase
  have hB : 0 < B := by have := hF 1; dsimp only [B]; linarith
  let numeric : IncrementSecondaryReferenceBudget Ref hd hs theta packet := {
    nativeInverse := Inverse
    nativeInverse_nonneg := hI
    cF := lower/B^2
    cT := (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2
    MH := actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2)
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    cT_pos := sq_pos_of_pos (div_pos hKernel (mul_pos (sq_pos_of_pos hB)
      (actualIncrementSortedSymmetricConstant_pos m)))
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hI 1)
      (mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2)
    first_value := fun r i a => (hNumbers r i a).1
    transverse_value := fun r i a => (hNumbers r i a).2.1
    hessian_bound := fun r i a => (hNumbers r i a).2.2.1.le
    inverse_bound := by
      intro r i a j hj hj2
      exact le_of_eq (congrFun (hNumbers r i a).2.2.2.2.1 j) }
  refine ⟨packet,numeric,rfl,rfl,rfl,rfl,hCard,
    fun r i a => ⟨(hNumbers r i a).2.2.2.1,(hNumbers r i a).2.2.2.2.1,
      (hNumbers r i a).2.2.2.2.2⟩,hCut,hSamples,?_⟩
  intro r i a y hy
  have hs := (piece r i a).carrier_source hy
  have heval := (actual_original_native_evaluation_iff Ref hd i
    (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1) y)).mp
      (hSamples r i a _ hs.2)
  exact heval.2.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_parameter_secondary_numerical_packet
