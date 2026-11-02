import Repair.FullIncrementNovOpenNativePresentation
import Probes.Round3ParameterNativeRefinementSamples

/-! The actual observer mean preparation, retaining the given datum and its
original compact parameter set.  Every chart/slice is the genuine nonlinear
conjugate of the supplied physical piece.  Refinement samples are transported
by their computational fields, and transverse coercivity by equality of the
same physical open-parameter slice.  Neither step requires `K = univ`.

This construction is the local geometric bridge.  The global canonical-mean
consumer still needs a local-operator coherence bridge in place of its old
whole-family HEq contract; that consumer is not asserted here.
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
local notation "X" => Ep × D
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem fullIncrementNov_refinement_samples_of_same_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    {Sub : Type*} [Fintype Sub] {F F' : Ep → M → Ey}
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub) F')
    (hCut : g.cutoff = g'.cutoff) (hEta : g.eta = g'.eta) (hChart : g.chart = g'.chart)
    (host : Fin Data.primaryCount → Sub → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X)
    (W : Set (Ep × M)) (ell : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ)
    (h : Round3ParameterRefinementSamples Data ip F g host b W ell Tinv Forward Meta Rsub Lprimary) :
    Round3ParameterRefinementSamples Data ip F' g' host b W ell Tinv Forward Meta Rsub Lprimary := by
  have hActive (observer nu beta) :
      round3ParameterRefinementActive Data ip F g W observer nu beta =
      round3ParameterRefinementActive Data ip F' g' W observer nu beta := by
    unfold round3ParameterRefinementActive
    rw [hCut,hEta]
  have hSample (observer nu beta) :
      round3ParameterRefinementSample Data ip F g W observer nu beta =
      round3ParameterRefinementSample Data ip F' g' W observer nu beta := by
    unfold round3ParameterRefinementSample
    rw [hChart,hActive]
  refine {
    eta_smooth := ?_
    eta_support := ?_
    partition := ?_
    sample_inverse := ?_
    inverse_jets := ?_
    forward_jets := ?_
    eta_jets := ?_
    eta_count := ?_
    primary_count := ?_ }
  · simpa only [hEta] using h.eta_smooth
  · simpa only [hEta,hChart] using h.eta_support
  · simpa only [hCut,hEta] using h.partition
  · simpa only [hSample] using h.sample_inverse
  · simpa only [hSample] using h.inverse_jets
  · simpa only [hActive] using h.forward_jets
  · simpa only [hSample,hEta,hChart] using h.eta_jets
  · simpa only [hEta] using h.eta_count
  · simpa only [hCut] using h.primary_count

theorem fullIncrementNov_original_open_native_mean_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (Ep × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a))
    (hInner : ∀ nu a y,
      y ∈ (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native).source →
      y.2 ∈ Data.atlas.inner (piece nu a).host)
    (R : ℕ)
    (hGeometry : Round3ParameterOriginalPrimaryGeometry Data
      (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Data
      (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) Forward Inverse Meta)
    (ell cT : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hNative : ∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data ((piece nu a).host,ip nu a) z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs ((piece nu a).host,ip nu a) z.1)
        ((piece nu a).slices z.1).symm z.2 v‖^2)
    (observer : Fin Data.atlas.count × Fin Data.parameterCount) :
    let g := round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart observer.2)
    let host := fun nu a => (piece nu a).host
    let b := fun nu a => round3ParameterCrossNativeChart (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (piece nu a).native
    ∃ (e : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D)
      (hdata : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart observer.2).symm z.1,z.2)) (e nu a))
      (hactive : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
        ((Data.parameterChart observer.2).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      let actual := actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive
      (∀ nu a, (b nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,observer.2)) ∧
      actual.phase = gN.phase ∧ actual.cutoff = gN.cutoff ∧ actual.normal = gN.normal ∧
      actual.linearArgument = gN.linearArgument ∧ actual.eta = gN.eta ∧
      actual.chart = gN.chart ∧ actual.inverse = gN.inverse ∧
      Round3ParameterRefinementSamples Data observer.2 (actualOriginalOpenParameterSlice Data observer)
        actual host b ((Data.parameterChart observer.2).target ×ˢ (univ : Set M)) ell Inverse
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount ∧
      ∀ nu a z, z ∈ (b nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data observer z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs observer z.1) (e nu a z.1).symm z.2 v‖^2 := by
  intro g gN host b
  obtain ⟨e,hdata,hactive,hNativeOpen,hSlices,hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverse⟩ :=
    fullIncrementNov_original_open_native_presentation Data hd hs hn ip W piece observer
  let actual := actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive
  have hChart' (nu) (a) : actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) = gN.chart nu a :=
    congrFun (congrFun hChart nu) a
  have hSource (nu) (a) : (b nu a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu a))).target := by
    intro z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data (host nu a,observer.2) z).mp
      (hNativeOpen nu a hz)).1⟩
  have hInnerNative (nu) (a) (y : Ep × M) (hy : y ∈ (gN.chart nu a).source) :
      y.2 ∈ Data.atlas.inner (host nu a) := by
    have h1 := (round3ParameterChartPullback_source (Data.parameterChart observer.2)
      (g.chart nu a) y).mp hy
    have h2 := (round3ParameterChartPullback_source (Data.parameterChart (ip nu a)).symm
      (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native)
      ((Data.parameterChart observer.2).symm y.1,y.2)).mp h1.2.1
    exact hInner nu a ((Data.parameterChart (ip nu a)) ((Data.parameterChart observer.2).symm y.1),y.2) h2.2.1
  have hRefinement := round3Parameter_native_original_refinement_samples Data hd g R hGeometry observer.2
    host b hChart' hSource hInnerNative Forward Inverse Meta hProfiles ell hell hell1
    ((Data.parameterChart observer.2).target ×ˢ (univ : Set M))
    ((Data.parameterChart observer.2).open_target.prod isOpen_univ) Subset.rfl
  refine ⟨e,hdata,hactive,hNativeOpen,hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverse,?_,?_⟩
  · exact fullIncrementNov_refinement_samples_of_same_fields Data observer.2 gN actual
      hCut.symm hEta.symm hChart.symm host b _ ell Inverse _ _ R Data.primaryCount hRefinement
  · intro nu a z hz v
    exact (fullIncrementNov_original_open_cross_transverse_reserve Data hd hs (ip nu a) observer
      nu (W nu a) (piece nu a) (e nu a) (hSlices nu a) cT (hNative nu a) z hz v).2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_refinement_samples_of_same_fields
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_native_mean_preparation
