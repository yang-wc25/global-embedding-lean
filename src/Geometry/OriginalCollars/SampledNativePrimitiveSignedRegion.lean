import OriginalCollars.NativePrimitiveSignedRegion
import OriginalCollars.SampledSignedHostRefinement
import OriginalIncrements.NativeNumericalSecondaryPiece
import Repair.IncrementActualSignedRefinement

/-!
# Signed primitive geometry without samples on the construction open set

All native map and phase bounds concern the actual original functions on
an open domain. Observation samples are supplied at the actual carrier by
the separate pointwise observer theorem. The construction domain is never
required to lie in K, Omega or Q. The single counted grid, physical centers,
literal cutoffs and signed pieces retain all the same numerical identities.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance sampledNativePrimitiveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance sampledNativePrimitiveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

variable [T2Space M]

theorem sampled_native_primitive_signed_numerical_refinement
    (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hFirstBudget : Phase 1 ≤ Mb) (hSecondBudget : buffer*Phase 2 ≤ Mb)
    (hKernel : 0 < kernel) (hLower : 0 < lower) (hNativeTwo : 0 ≤ nativeTwo)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount))
    (W : Set (Ep × M)) (hW : IsOpen W)
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).source)
    (region : NativePrimitiveSignedRegion Ref i r W theta mu R buffer coordinateBound kernel lower nativeTwo Phase) :
    ∃ (s : Finset X) (out : s → Round3PreparedSignedReferencePiece Ref hd hs i r W),
      let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
      let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
      let B := 1+Forward 1
      let radius := buffer/actualPhaseRefinementFactor mu Mb
      s.card ≤ countedSignedTotalRefinementBound («Ep» := Ep) (m := m)
        mu Mb R buffer hmu hMb hbuffer ∧
      (↑s : Set X) ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)) ''
        (tsupport theta ∩ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W) ∧
      (∀ y ∈ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W,
        ∑ a : s, (out a).cutoff y = theta y) ∧
      (∀ a : s, tsupport (out a).cutoff ⊆ tsupport theta) ∧
      (∀ y, (Finset.univ.filter (fun a : s => y ∈ (out a).carrier)).card ≤ 5^Module.finrank ℝ X) ∧
      (∀ a : s, (out a).cF = lower/B^2 ∧
        (out a).cT = (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2 ∧
        (out a).MH = actualFirstFrameTransferCost Inverse 1*nativeTwo ∧
        (out a).Forward = Forward ∧ (out a).Tinv = Inverse ∧
        (out a).cutoff = actualHostRefinementCutoff
          (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)) theta
          (actualRefinementCutoff X s radius a.val)) ∧
      (∀ j (weight : ℝ), 0 ≤ weight → weight ≤ buffer → ∀ (a : s) (x : X),
        weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s radius a.val) x‖ ≤
          (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j) ∧
      (∀ a : s, ActualPhaseSampleJetControls mu Mb
        ((actualOriginalParameterSignedPhase Ref i r.val) ∘
          (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).symm)
        (out a).native) := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)
  let pair := actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W
  let K := q '' (tsupport theta ∩ pair)
  have hRelative : incrementsGlobalRelativeSupport W theta = W ∩ tsupport theta :=
    parameterRound2_global_relativeSupport_eq W hW theta
  have hRelativeSource : incrementsGlobalRelativeSupport W theta ⊆ q.source := by
    rw [hRelative]
    exact fun _ hz => (hThetaSupport hz.2).2
  obtain ⟨s,b,e,hcard,hCenters,hdata,hbO,hSourceW,hCompactEta,hSmoothEta,hSupportEta,hPartition,hCount,hForward,hInverse,hCut,hControls⟩ :=
    sampled_signed_host_interaction_complete_profiles mu Mb R buffer coordinateBound Phase
      hmu hMb hbuffer hCoordinate hPhase hFirstBudget hSecondBudget
      (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1) theta
      (actualOriginalParameterSignedPhase Ref i r.val) W pair hW hTheta.contMDiffOn
      K region.domain region.center hRelativeSource
      (fun y hy => ⟨y,⟨(hRelative ▸ hy.1).2,hy.2⟩,rfl⟩)
      region.isOpen region.carrier_radius region.target region.parent region.carrier_buffer
      region.phase_smooth region.phase_noncritical region.coordinates region.phase_jets
  let radius := buffer/actualPhaseRefinementFactor mu Mb
  let eta := fun a : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s radius a.val)
  let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
  let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
  have hF : ∀ j, 0 ≤ Forward j := incrementScalarForwardProfile_nonneg Mb coordinateBound Phase hMb hCoordinate hPhase
  have hI : ∀ j, 0 ≤ Inverse j := incrementScalarInverseProfile_nonneg mu Mb coordinateBound Phase hmu hMb hCoordinate hPhase
  have hEtaTheta (a : s) : tsupport (eta a) ⊆ tsupport theta := by
    intro y hy
    exact (hRelative ▸ (hSupportEta a hy).2).2
  have hActive (a : s) (y : Ep × M) (hy : y ∈ (actualHostAdaptedChart (Ref.atlas.chart i.1) (b a)).source) :
      ((Ref.parameterChart i.2).symm y.1,y.2) ∈ Ref.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Ref ∧
      ((Ref.parameterChart i.2).symm y.1,y.2) ∈ Ref.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Ref := by
    have hz := region.active (hbO a hy.2)
    have hnu := round3_prepared_native_primary_active Ref i r.val.1.1 hz.1
    have hmu := round3_prepared_native_primary_active Ref i r.val.1.2 hz.2
    change ((Ref.parameterChart i.2).symm y.1,(Ref.atlas.chart i.1).symm ((Ref.atlas.chart i.1) y.2)) ∈ _ at hnu hmu
    rw [(Ref.atlas.chart i.1).left_inv hy.1.2] at hnu hmu
    exact ⟨hnu,hmu⟩
  have hInner (a : s) (y : Ep × M) (hy : y ∈ (actualHostAdaptedChart (Ref.atlas.chart i.1) (b a)).source) :
      y.2 ∈ Ref.atlas.inner i.1 := by
    have h := region.inner _ (hbO a hy.2)
    change (Ref.atlas.chart i.1).symm ((Ref.atlas.chart i.1) y.2) ∈ _ at h
    rwa [(Ref.atlas.chart i.1).left_inv hy.1.2] at h
  let out : s → Round3PreparedSignedReferencePiece Ref hd hs i r W := fun a =>
    OriginalIncrements.nativeNumericalSecondaryPiece Forward Inverse hF hI lower nativeTwo kernel hLower hNativeTwo hKernel
      Ref hd hs i r W (b a) (e a) (hdata a)
      (eta a) (hCompactEta a) (hSmoothEta a) (fun _ hz => (hSupportEta a hz).1)
      (fun _ hz => round3_prepared_primary_native_subset Ref i r.val.1.1 (region.active (hbO a hz)).1)
      (hSourceW a) (hActive a) (hInner a) (fun j => hForward j a) (fun j => hInverse j a)
      (fun z hz => region.native_first z (hbO a hz))
      (fun k hk z hz => region.native_jets k hk z (hbO a hz))
      (fun z hz => region.original_kernel z (hbO a hz))
  refine ⟨s,out,hcard,hCenters,?_,hEtaTheta,?_,?_,hCut,hControls⟩
  · intro y hy
    have hyW : y ∈ W := by
      obtain ⟨z,_,rfl⟩ := hy.1
      exact z.property
    exact hPartition y ⟨hyW,hy⟩
  · intro y
    apply (Finset.card_le_card (show
      Finset.univ.filter (fun a : s => y ∈ (out a).carrier) ⊆
      Finset.univ.filter (fun a : s => y ∈ tsupport (eta a)) from ?_)).trans (hCount y)
    intro a ha
    have hh := (out a).carrier_eq ▸ (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩
  · intro a
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.sampled_native_primitive_signed_numerical_refinement
