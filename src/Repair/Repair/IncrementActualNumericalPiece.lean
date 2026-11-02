import Repair.IncrementNumericalSecondaryPacket

/-!
# The literal nonlinear signed chart produces one numerical secondary piece

The native map, slices and cutoff supplied by the actual scalar refinement
are retained exactly. Original host C2, ellipticity, original kernel margin,
and the already constructed native derivatives produce every quantitative
field. No adapted frame, Hessian bound, or conditioned chart is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance actualPieceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance actualPieceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def incrementActualNumericalSecondaryPiece
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower C2 kernel : ℝ) (hLower : 0 < lower) (hC2 : 0 ≤ C2) (hKernel : 0 < kernel)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Ref.atlas.chart i.1) b
      (actualOriginalParameterSignedPhase Ref i r.val) e)
    (rho : Ep × M → ℝ) (hCompact : IsCompact (tsupport rho))
    (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (hSupport : tsupport rho ⊆ (actualHostAdaptedChart (Ref.atlas.chart i.1) b).source)
    (hsource : b.source ⊆ actualOriginalNativeOpen Ref i)
    (hDomain : (actualHostAdaptedChart (Ref.atlas.chart i.1) b).source ⊆ W)
    (hactive : ∀ w ∈ (actualHostAdaptedChart (Ref.atlas.chart i.1) b).source,
      ((Ref.parameterChart i.2).symm w.1,w.2) ∈ Ref.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Ref ∧
      ((Ref.parameterChart i.2).symm w.1,w.2) ∈ Ref.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Ref)
    (hInner : ∀ w ∈ (actualHostAdaptedChart (Ref.atlas.chart i.1) b).source,
      w.2 ∈ Ref.atlas.inner i.1)
    (hForw : ∀ j z, z ∈ b.source → ‖iteratedFDeriv ℝ j b z‖ ≤ Forward j)
    (hInv : ∀ j z, z ∈ b.target → ‖iteratedFDeriv ℝ j b.symm z‖ ≤ Inverse j)
    (hSamples : ∀ z, z ∈ b.source → parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet i)
    (hMargin : ∀ y ∈ b.source, ∀ v, kernel*‖v‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Ref i)
        (fun _ => Ref.atlas.chart i.1) y)
      (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Ref i r.val
        (y.1,(Ref.atlas.chart i.1).symm x)) y.2) v‖) :
    Round3PreparedSignedReferencePiece Ref hd hs i r W := by
  let B := 1+Forward 1
  have hB : 0 < B := by dsimp only [B]; have := hForward 1; linarith
  let K := actualOriginalMapJetCost (m+1) d N 0*C2
  have hK : 0 ≤ K := mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2
  let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
    Ref.parameterNormDomain Ref.parameterSet
  have hSO : ∀ j, S j ⊆ incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart j :=
    fun _ _ hy => hy.1
  have hCoords := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Ref.F (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  let Fn := fun p x => Ref.F ((Ref.parameterChart i.2).symm p,x)
  have hJoint : ContDiffOn ℝ ∞ (fun z : X => Fn z.1 ((Ref.atlas.chart i.1).symm z.2)) b.source :=
    round4_original_native_host_joint_smooth Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
      i b.source hSamples
  have hNativeForward (y : X) (hy : y ∈ b.source) : ‖fderiv ℝ b y‖ ≤ B := by
    have h := hForw 1 y hy
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (by dsimp only [B]; linarith)
  have hLow := repairEntrance_native_original_low_budgets Fn
    (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
    b _ e hdata b.source b.open_source hJoint subset_rfl lower B K hLower hB hK
    Inverse hInverse (by
      intro z hz v
      have hSample := (actual_original_native_evaluation_iff Ref hd i z).mp (hSamples z hz)
      exact hEll.lower ((Ref.parameterChart i.2).symm z.1) hSample.2.2 i.1 z.2 hSample.1 v) (by
      intro k hk z hz
      exact round3_original_C2_native_jets Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
        hMapFinite C2 hMap i k hk z (hSamples z hz)) hNativeForward hInv
  have hSlice (z : X) : actualOriginalOpenParameterSlice Ref i z.1 = Fn z.1 :=
    actualOriginalOpenParameterSlice_eq Ref i z.1
      (hd.parameter_subset (by rw [hAll]; exact mem_univ _))
  have hFn : actualOriginalOpenParameterSlice Ref i = Fn := by
    funext p; exact hSlice (p,0)
  have hJoint' : ContDiffOn ℝ ∞ (fun z : X =>
      actualOriginalOpenParameterSlice Ref i z.1 ((Ref.atlas.chart i.1).symm z.2)) b.source := by
    rwa [hFn]
  let carrier := tsupport rho ∩ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W
  have hCarrierCompact : IsCompact carrier := actual_compact_interaction_carrier (tsupport rho) W hCompact
    (hSupport.trans hDomain)
    (fun z => Ref.cutoff r.val.1.1 ((Ref.parameterChart i.2).symm z.1,z.2))
    (fun z => Ref.cutoff r.val.1.2 ((Ref.parameterChart i.2).symm z.1,z.2))
  exact {
    native := b
    slices := e
    cutoff := rho
    carrier := carrier
    data := hdata
    native_source := hsource
    source_domain := hDomain
    active := hactive
    source_inner := hInner
    cutoff_compact := hCompact
    cutoff_smooth := hRho
    carrier_eq := rfl
    carrier_compact := hCarrierCompact
    carrier_source := inter_subset_left.trans hSupport
    cF := lower/B^2
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    cT := (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2
    cT_pos := sq_pos_of_pos (div_pos hKernel (mul_pos (sq_pos_of_pos hB)
      (actualIncrementSortedSymmetricConstant_pos m)))
    MH := actualFirstFrameTransferCost Inverse 1*K
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hInverse 1) hK
    Bnative := B
    Bnative_pos := hB
    native_first := hNativeForward
    first := by
      intro z hz v
      rw [hSlice]
      exact hLow.1 z hz v
    transverse := by
      intro z hz v
      exact repairEntrance_native_original_transverse_reserve
        (actualOriginalOpenParameterSlice Ref i)
        (actualOriginalOpenParameterSlice_contMDiff Ref hd hs i)
        (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
        b _ e hdata b.source b.open_source hJoint' subset_rfl
        kernel B hKernel.le hB hNativeForward z hz (hMargin (b.symm z) (b.map_target hz)) v
    hessian := by
      intro z hz
      rw [hSlice]
      exact hLow.2 z hz
    Tinv := Inverse
    Tinv_nonneg := hInverse
    inverse_jets := hInv
    Forward := Forward
    Forward_nonneg := hForward
    forward_jets := hForw }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementActualNumericalSecondaryPiece
