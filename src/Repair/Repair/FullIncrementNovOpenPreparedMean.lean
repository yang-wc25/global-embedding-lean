import Repair.FullIncrementNovOpenNativeMean
import Repair.FullIncrementNovOpenPrimaryGeometry
import Repair.FullIncrementNovOpenReferenceProfiles
import Repair.FullIncrementNovLocalRefinementSamples
import Probes.Round3ParameterWholePieceReplacement
import Probes.Round3ParameterWholePrimaryChartProfiles
import Smoothing.ParameterRound2CompactNorms

/-! A genuine local mean preparation for one fixed original datum.  The actual
conditioned pieces and all observer slices are selected once, before the scale
and derivative order.  No global equality of base maps outside parameterOpen
is asserted.  The seven computational fields agree, the local refinement is
proved on the genuine neighborhood, and the transverse reserve is transported
from the actually conditioned original pieces.

The compactly selected profiles here are qualitative all-order profiles.
Their uniform dependence on the original finite input prefix is a separate
remaining obligation; this file does not claim such a dependence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

structure FullIncrementNovOpenNativeMeanPreparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (G : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) where
  host : Fin Data.primaryCount → Sub → Fin Data.atlas.count
  native : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X
  slices : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D
  data : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (native nu a)
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (slices nu a)
  active : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (native nu a)).source →
    ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  native_open : ∀ nu a, (native nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,i.2)
  same_fields :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
    let actual := actualOriginalPrimaryFamily Data hd hs hn i host native slices data gN.eta active
    actual.phase = gN.phase ∧ actual.cutoff = gN.cutoff ∧ actual.normal = gN.normal ∧
      actual.linearArgument = gN.linearArgument ∧ actual.eta = gN.eta ∧
      actual.chart = gN.chart ∧ actual.inverse = gN.inverse
  refinement : ∀ ell, 0 ≤ ell → ell ≤ 1 →
    Round3ParameterRefinementSamples Data i.2 (actualOriginalOpenParameterSlice Data i)
      (actualOriginalPrimaryFamily Data hd hs hn i host native slices data
        (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta active)
      host native (actualOriginalParameterNeighborhood Data i.2 G)
      ell Tinv Forward Meta Rsub Data.primaryCount
  transverse : ∀ nu a z, z ∈ (native nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
    ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (slices nu a z.1).symm z.2 v‖^2

theorem fullIncrementNov_conditioned_open_piece_inner
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet)
    (nu : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet)
    (y : Ep × M)
    (hy : y ∈ (actualHostAdaptedChart
      (Data.atlas.chart (round3ParameterWholePrimaryPiece Data hd theta
        (packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff) nu a).host)
      (round3ParameterWholePrimaryPiece Data hd theta
        (packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff) nu a).native).source) :
    y.2 ∈ Data.atlas.inner (round3ParameterWholePrimaryPiece Data hd theta
      (packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff) nu a).host := by
  rcases a with ⟨i,mu,a⟩
  by_cases h : mu = nu
  · subst mu
    simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active,
      Round3ParameterWholePrimaryPieceSupply.replacePieces] at hy ⊢
    exact profiles.source_inner nu i a y hy
  · simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
      round3PreparedPrimaryEmpty,actualHostAdaptedChart,OpenPartialHomeomorph.trans_source,
      round3PreparedEmptyNativeChart_source,preimage_empty,inter_empty,mem_empty_iff_false] at hy

theorem fullIncrementNov_conditioned_open_piece_transverse
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet)
    (nu : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) :
    let piece := round3ParameterWholePrimaryPiece Data hd theta
      (packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff) nu a
    ∀ z ∈ piece.native.target, ∀ v : Tdata, profiles.cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data (piece.host,a.1.2) z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs (piece.host,a.1.2) z.1)
        (piece.slices z.1).symm z.2 v‖^2 := by
  intro piece z hz v
  rcases a with ⟨i,mu,a⟩
  by_cases h : mu = nu
  · subst mu
    simp only [piece,round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active,
      Round3ParameterWholePrimaryPieceSupply.replacePieces] at hz ⊢
    exact profiles.transverse nu i a z hz v
  · simp only [piece,round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
      round3PreparedPrimaryEmpty,round3PreparedEmptyNativeChart_target,mem_empty_iff_false] at hz

theorem fullIncrementNov_conditioned_open_mean_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet)
    (V : Set P) (hV : IsOpen V) (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
    (R : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i)) :
    let conditioned := packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta ∧
      ∀ i, Nonempty (FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
        (V ×ˢ (univ : Set M)) profiles.cT Inverse
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
        (R*5^Module.finrank ℝ (Ep × D)) i) := by
  intro conditioned g
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain univ
  have hS (i) : IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact
    Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain hOmega hQ
    hd.source_norm_subset hd.parameter_norm_subset i
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfilesFull⟩ :=
    round3Parameter_actual_whole_primary_chart_profiles Data hd hs hn theta conditioned S hS (fun _ _ hz => hz.1)
  have hProfiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta := by
    intro ell hell hell1 nu a i gN t etaN k z hz he
    exact hProfilesFull ell hell hell1 nu a i k z ⟨hz.1,hz.2.1,hz.2.2.1,mem_univ _⟩ he
  refine ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfiles,?_⟩
  intro observer
  let ip := fun (_ : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta conditioned) => a.1.2
  let W := fun (_ : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta conditioned) =>
    (Data.parameterChart a.1.2).target ×ˢ (univ : Set M)
  let piece := round3ParameterWholePrimaryPiece Data hd theta conditioned
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart observer.2)
  let host := fun nu a => (piece nu a).host
  let b := fun nu a => round3ParameterCrossNativeChart (Data.parameterChart (ip nu a))
    (Data.parameterChart observer.2) (piece nu a).native
  obtain ⟨e,hdata,hactive,hNative,hSlices,hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverseEq⟩ :=
    fullIncrementNov_original_open_native_presentation Data hd hs hn ip W piece observer
  let actual := actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive
  have hChart' (nu) (a) : actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) = gN.chart nu a :=
    congrFun (congrFun hChart nu) a
  have hSource (nu) (a) : (b nu a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu a))).target := by
    intro z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data (host nu a,observer.2) z).mp
      (hNative nu a hz)).1⟩
  have hInnerNative (nu) (a) (y : Ep × M) (hy : y ∈ (gN.chart nu a).source) :
      y.2 ∈ Data.atlas.inner (host nu a) := by
    have h1 := (round3ParameterChartPullback_source (Data.parameterChart observer.2) (g.chart nu a) y).mp hy
    have h2 := (round3ParameterChartPullback_source (Data.parameterChart (ip nu a)).symm
      (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native)
      ((Data.parameterChart observer.2).symm y.1,y.2)).mp h1.2.1
    exact fullIncrementNov_conditioned_open_piece_inner Data hd hs theta packet profiles nu a
      ((Data.parameterChart (ip nu a)) ((Data.parameterChart observer.2).symm y.1),y.2) h2.2.1
  refine ⟨{
    host := host
    native := b
    slices := e
    data := hdata
    active := hactive
    native_open := hNative
    same_fields := ⟨hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverseEq⟩
    refinement := ?_
    transverse := ?_ }⟩
  · intro ell hell hell1
    let G := actualOriginalParameterNeighborhood Data observer.2 (V ×ˢ (univ : Set M))
    have hG : IsOpen G := actualOriginalParameterNeighborhood_isOpen Data observer.2 _ (hV.prod isOpen_univ)
    have hRefinement := fullIncrementNov_native_refinement_samples_from_local_geometry Data hd g
      (R*5^Module.finrank ℝ (Ep × D)) observer.2 host b hChart' hSource hInnerNative
      Forward Inverse Meta hProfiles ell hell hell1 G hG inter_subset_left
      (fullIncrementNov_whole_primary_open_native_geometry Data hd hs hn theta conditioned V hV hPart R hCount observer.2)
    exact fullIncrementNov_refinement_samples_of_same_fields Data observer.2 gN actual
      hCut.symm hEta.symm hChart.symm host b G ell Inverse _ _ _ Data.primaryCount hRefinement
  · intro nu a z hz v
    exact (fullIncrementNov_original_open_cross_transverse_reserve Data hd hs (ip nu a) observer
      nu (W nu a) (piece nu a) (e nu a) (hSlices nu a) profiles.cT
      (fullIncrementNov_conditioned_open_piece_transverse Data hd hs theta packet profiles nu a) z hz v).2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_conditioned_open_piece_inner
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_conditioned_open_piece_transverse
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_conditioned_open_mean_preparation
