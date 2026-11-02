import Repair.FullIncrementNovOpenPrimaryPieces
import Repair.FullIncrementNovOpenParameterTransverse
import Probes.Round3ParameterWholeReferenceProfiles
import Probes.ActualIncrementOriginalMeanPrimitives

/-! Actual compact conditioning of the original map on its original open
parameter region.  The existing reference-profile record is produced without
global smoothness of F or K = univ.  The local domain annotation is used only
to feed the original smoothness proof to the existing target restriction.
All chart functions, inverse functions, cutoffs and given primitives remain
those of the original packet.  Compactness produces real positive reserves;
this does not claim their still missing uniform finite-input-prefix bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def fullIncrementNovPrimaryPieceOpenAnnotation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (piece : Round3PreparedPrimaryPiece Data ip nu
      ((Data.parameterChart ip).target ×ˢ (univ : Set M))) :
    Round3PreparedPrimaryPiece Data ip nu
      (actualOriginalParameterNeighborhood Data ip (incrementsOriginalParameterRegion Data)) where
  host := piece.host
  native := piece.native
  slices := piece.slices
  cutoff := piece.cutoff
  data := piece.data
  native_source := piece.native_source
  source_domain := fun z hz => ⟨piece.source_domain hz,(piece.active z hz).2⟩
  active := piece.active
  compact := piece.compact
  smooth := piece.smooth
  support := piece.support
  Bnative := piece.Bnative
  positive := piece.positive
  native_first := piece.native_first

theorem fullIncrementNov_original_open_reference_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (hInner : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
      y.2 ∈ Data.atlas.inner (packet.piece nu i a).host) :
    Nonempty (Round3ParameterWholeReferenceProfiles Data hd hs theta packet) := by
  obtain ⟨cF,cT,piece,hcF,hcT,hHost,hCut,hb,hbi,hSlices,hFirst,hFrame⟩ :=
    round3Parameter_actual_whole_reference_conditioning Data hd hs hp hImm theta packet
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let G := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    actualOriginalParameterNeighborhood Data i.2 (incrementsOriginalParameterRegion Data)
  let Fn := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) p x =>
    Data.F ((Data.parameterChart i.2).symm p,x)
  have hFn (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry (Fn i)) (G i) :=
    actual_original_parameter_pullback_smooth Data hd i.2 Data.F
      (incrementsOriginalParameterRegion Data) hs.F_joint (G i)
      (fun _ hz => hz.1.1) (fun _ hz => hz.2)
  let localPiece := fun nu i (a : packet.s nu i) =>
    fullIncrementNovPrimaryPieceOpenAnnotation Data i.2 nu (piece nu i a)
  have hInner' (nu) (i) (a : packet.s nu i) (y : Ep × M)
      (hy : y ∈ tsupport (localPiece nu i a).cutoff) :
      y.2 ∈ Data.atlas.inner (localPiece nu i a).host := by
    change y.2 ∈ Data.atlas.inner (piece nu i a).host
    rw [hHost]
    exact hInner nu i a y (by change y ∈ tsupport (piece nu i a).cutoff at hy; rwa [hCut] at hy)
  have hLocal (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (a : packet.s nu i) :=
    round3_prepared_primary_reference_target_profiled Data hd i.2 nu (G i) (localPiece nu i a)
      (hInner' nu i a) (Fn i) (hFn i)
  choose MH out Ti Tf hMH hHost' hCut' hb' hbi' hSlices' hTarget hBN hHessian hTi hTf hInv hForw hSourceInner using hLocal
  let final := fun nu i (a : packet.s nu i) =>
    fullIncrementNovPrimaryPieceEnlarge Data i.2 nu (G i) (W i) (out nu i a) inter_subset_left
  let Index := Sigma (fun nu : Fin Data.primaryCount =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s nu i)))
  let MHmax := round3PreparedFiniteMaximum (fun a : Index => MH a.1 a.2.1 a.2.2)
  let Tinv := fun j => round3PreparedFiniteMaximum (fun a : Index => Ti a.1 a.2.1 a.2.2 j)
  let Tforward := fun j => round3PreparedFiniteMaximum (fun a : Index => Tf a.1 a.2.1 a.2.2 j)
  refine ⟨{
    piece := final
    host := fun nu i a => (hHost' nu i a).trans (hHost nu i a)
    cutoff := fun nu i a => (hCut' nu i a).trans (hCut nu i a)
    forward := fun nu i a => (hb' nu i a).trans (hb nu i a)
    inverse := fun nu i a => (hbi' nu i a).trans (hbi nu i a)
    slices := fun nu i a p => (hSlices' nu i a p).trans (hSlices nu i a p)
    cF := cF
    cT := cT
    MH := MHmax
    cF_pos := hcF
    cT_pos := hcT
    MH_nonneg := round3PreparedFiniteMaximum_nonneg _
    Tinv := Tinv
    Tforward := Tforward
    Tinv_nonneg := fun _ => round3PreparedFiniteMaximum_nonneg _
    Tforward_nonneg := fun _ => round3PreparedFiniteMaximum_nonneg _
    first := ?_
    transverse := ?_
    hessian := ?_
    inverse_jets := ?_
    forward_jets := ?_
    source_inner := hSourceInner }⟩
  · intro nu i a z hz v
    have hh := hFirst nu i a z (hTarget nu i a hz) v
    have hOpen := fullIncrementNov_primary_target_parameter_open Data hd i.2 nu (G i)
      (out nu i a) z hz
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 hOpen] at hh
    change cF*‖v‖^2 ≤ ‖fderiv ℝ ((Fn i z.1) ∘ ((out nu i a).slices z.1).symm) z.2 v‖^2
    rw [hSlices']
    exact hh
  · intro nu i a z hz v
    change cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
      ((out nu i a).slices z.1).symm z.2 v‖^2
    rw [hSlices']
    exact hFrame nu i a z (hTarget nu i a hz) v
  · intro nu i a z hz
    exact (hHessian nu i a z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => MH a.1 a.2.1 a.2.2) ⟨nu,i,a⟩)
  · intro nu i a j z hz
    exact (hInv nu i a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => Ti a.1 a.2.1 a.2.2 j) ⟨nu,i,a⟩)
  · intro nu i a j z hz
    exact (hForw nu i a j z hz).trans (round3PreparedFiniteMaximum_bound
      (fun a : Index => Tf a.1 a.2.1 a.2.2 j) ⟨nu,i,a⟩)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryPieceOpenAnnotation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_reference_profiles
