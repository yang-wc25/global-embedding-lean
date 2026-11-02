import Repair.IncrementActualNumericalPiece

/-! Numerical signed pieces from the original map on its genuine open
native region. Compact parameter samples are never required to contain
an open neighborhood. The original parameter set may be a proper compact
set, including one with empty interior. Only original native two-jets,
spatial ellipticity and the actual chosen signed-phase restriction enter.
The actual chart, slices, cutoff and carrier are retained exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance nativePieceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativePieceSquareNormed {E : Type*}
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

/-- The original native two-jets transfer on the same open region. This
uses a neighborhood equality, so all derivatives agree, even when the
compact parameter set itself has no interior. -/
theorem original_open_slice_native_two_jets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (O : Set X) (hO : O ⊆ actualOriginalNativeOpen Ref i)
    (K : ℝ)
    (hJets : ∀ k ≤ 2, ∀ z ∈ O, ‖iteratedFDeriv ℝ k (actualOriginalNativeMap Ref i) z‖ ≤ K) :
    ∀ k ≤ 2, ∀ z ∈ O,
      ‖iteratedFDeriv ℝ k (fun y : X =>
        actualOriginalOpenParameterSlice Ref i y.1 ((Ref.atlas.chart i.1).symm y.2)) z‖ ≤ K := by
  intro k hk z hz
  have hEq := Filter.eventuallyEq_of_mem
    ((actualOriginalNativeOpen_isOpen Ref hd i).mem_nhds (hO hz))
    (actualOriginalOpenParameterSlice_native_eqOn Ref i)
  rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hJets k hk z hz

def nativeNumericalSecondaryPiece
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower K kernel : ℝ) (hLower : 0 < lower) (hK : 0 ≤ K) (hKernel : 0 < kernel)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
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
    (hFirst : ∀ z ∈ b.source, ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ
        (actualOriginalParameterSlice Ref i z.1 ∘ (Ref.atlas.chart i.1).symm) z.2 v‖^2)
    (hJets : ∀ k ≤ 2, ∀ z ∈ b.source,
      ‖iteratedFDeriv ℝ k (actualOriginalNativeMap Ref i) z‖ ≤ K)
    (hMargin : ∀ y ∈ b.source, ∀ v, kernel*‖v‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Ref i)
        (fun _ => Ref.atlas.chart i.1) y)
      (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Ref i r.val
        (y.1,(Ref.atlas.chart i.1).symm x)) y.2) v‖) :
    Round3PreparedSignedReferencePiece Ref hd hs i r W := by
  let B := 1+Forward 1
  have hB : 0 < B := by dsimp only [B]; have := hForward 1; linarith
  let Fn := actualOriginalOpenParameterSlice Ref i
  have hJoint : ContDiffOn ℝ ∞ (fun z : X => Fn z.1 ((Ref.atlas.chart i.1).symm z.2)) b.source :=
    (actualOriginalOpenParameterSlice_native_contDiffOn Ref hd hs i).mono hsource
  have hNativeForward (y : X) (hy : y ∈ b.source) : ‖fderiv ℝ b y‖ ≤ B := by
    have h := hForw 1 y hy
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (by dsimp only [B]; linarith)
  have hFirst' (z : X) (hz : z ∈ b.source) (v : D) :
      lower*‖v‖^2 ≤ ‖fderiv ℝ (Fn z.1 ∘ (Ref.atlas.chart i.1).symm) z.2 v‖^2 := by
    dsimp only [Fn]
    rw [actualOriginalOpenParameterSlice_eq Ref i z.1
      (actualOriginalNativeOpen_parameter Ref i (hsource hz))]
    exact hFirst z hz v
  have hLow := repairEntrance_native_original_low_budgets Fn
    (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
    b _ e hdata b.source b.open_source hJoint subset_rfl lower B K hLower hB hK
    Inverse hInverse hFirst'
    (original_open_slice_native_two_jets Ref hd i b.source hsource K hJets)
    hNativeForward hInv
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
    first := hLow.1
    transverse := by
      intro z hz v
      exact repairEntrance_native_original_transverse_reserve
        Fn (actualOriginalOpenParameterSlice_contMDiff Ref hd hs i)
        (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
        b _ e hdata b.source b.open_source hJoint subset_rfl
        kernel B hKernel.le hB hNativeForward z hz (hMargin (b.symm z) (b.map_target hz)) v
    hessian := hLow.2
    Tinv := Inverse
    Tinv_nonneg := hInverse
    inverse_jets := hInv
    Forward := Forward
    Forward_nonneg := hForward
    forward_jets := hForw }

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_open_slice_native_two_jets
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.nativeNumericalSecondaryPiece
