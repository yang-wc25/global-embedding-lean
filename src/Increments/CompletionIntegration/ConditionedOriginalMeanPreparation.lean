import CompletionIntegration.OriginalPrimaryProfiles
import CollarCompletion.PositivePrimaryLocalRefinement
import Repair.FullIncrementNovOpenPreparedMean

/-!
# Actual original open mean preparation without compact observation domains

The same conditioned pieces supply all numerical profiles internally. The
local partition remains local to V, and the unchanged original native mean
record is constructed with its seven exact fields and its actual transverse
reserve. Original Omega/Q are not compactified, and no observed chart or
cutoff profile is assumed. Uniform finite-entrance dependence of the actual
conditioning and the original raw collar construction remains unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open CollarCompletion
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

theorem completion_conditioned_original_mean_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet)
    (V : Set P) (hV : IsOpen V) (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
    (R : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (psi : P → ℝ)
    (hTheta : theta = fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)) :
    let conditioned := packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      OriginalPrimaryPositiveChartProfiles Data g Forward Inverse Meta ∧
      ∀ i, Nonempty (FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
        (V ×ˢ (univ : Set M)) profiles.cT Inverse
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
        (R*5^Module.finrank ℝ (Ep × D)) i) := by
  intro conditioned g
  have hProfilesActual := completion_original_primary_profiles Data hd hs hn B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg hSpatialNonneg
    transition psi
  rw [← hTheta] at hProfilesActual
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfiles⟩ := hProfilesActual packet profiles
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
    have hRefinement := original_primary_positive_refinement_samples_from_local_geometry Data hd g
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
#print axioms GlobalEmbedding.Continuation.completion_conditioned_original_mean_preparation
