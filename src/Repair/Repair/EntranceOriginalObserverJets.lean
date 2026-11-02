import Repair.EntrancePointwiseComposition
import Repair.ReferenceRehostedChart
import Probes.Round3ParameterCrossNativeRegularity

/-!
# Numerical jets of the actual original observer chart

Only positive derivatives of original atlas transitions are read, at
points in the original norm domains.  Native reference charts retain all
orders.  The zero order uses the fixed observer coordinate bounds.  No
maximum over the actual phase pieces or the reference map is selected.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
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
local notation "𝓙" => 𝓘(ℝ,D)

structure RepairOriginalTransitionBudgets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (Parameter Spatial : ℕ → ℝ) : Prop where
  parameter : ∀ ip jp k, 1 ≤ k → ∀ z : X,
    z.1 ∈ Ref.parameterNormDomain ip →
    z ∈ (((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).prod
      (OpenPartialHomeomorph.refl D)).source →
    ‖iteratedFDeriv ℝ k (((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).prod
      (OpenPartialHomeomorph.refl D)) z‖ ≤ Parameter k
  spatial : ∀ i j k, 1 ≤ k → ∀ z : X,
    z.2 ∈ Ref.sourceNormDomain i →
    z ∈ (repairReferenceHostTransition (Ref.atlas.chart i) (Ref.atlas.chart j)).source →
    ‖iteratedFDeriv ℝ k (repairReferenceHostTransition (Ref.atlas.chart i) (Ref.atlas.chart j)) z‖ ≤ Spatial k

def repairEntranceOriginalForwardProfile (Bp : ℝ) (Native Parameter Spatial : ℕ → ℝ) (j : ℕ) :=
  if j=0 then max Bp (Native 0) else
    repairEntranceCompositionProfile (repairEntranceConjugatedForwardProfile Native Parameter Parameter) Spatial j

def repairEntranceOriginalInverseProfile (Bp Bs : ℝ) (Native Parameter Spatial : ℕ → ℝ) (j : ℕ) :=
  if j=0 then max Bp Bs else
    repairEntranceCompositionProfile Spatial (repairEntranceConjugatedForwardProfile Native Parameter Parameter) j

private theorem entranceParameterTransition_smooth
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (ip jp : Fin Ref.parameterCount) :
    let C := ((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).prod
      (OpenPartialHomeomorph.refl D)
    ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target := by
  intro C
  have hf : ContDiffOn ℝ ∞ ((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp))
      ((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).source :=
    (round3Parameter_partial_trans_smooth (Ref.parameterChart ip).symm (Ref.parameterChart jp)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth ip))
      (contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth jp))).contDiffOn
  have hi : ContDiffOn ℝ ∞ ((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).symm
      ((Ref.parameterChart ip).symm.trans (Ref.parameterChart jp)).target :=
    (round3Parameter_partial_trans_symm_smooth (Ref.parameterChart ip).symm (Ref.parameterChart jp)
      (contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth ip))
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth jp))).contDiffOn
  exact ⟨hf.prodMap contDiff_id.contDiffOn,hi.prodMap contDiff_id.contDiffOn⟩

/-- The original observer-to-adapted function and its actual inverse at
one original sample. Every hypothesis is a primitive reference-chart or
original transition bound; neither observed output estimate is assumed. -/
theorem repairEntrance_original_native_observer_jets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (host : Fin Ref.atlas.count)
    (native : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (slices : Ep → OpenPartialHomeomorph M D)
    (data : ActualOriginalHostSliceData (Ref.atlas.chart host) native psi slices)
    (hNativePreserves : Round3ParameterChartPreserves native)
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hNI : ∀ j, 0 ≤ NI j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (hForward : ∀ j z, z ∈ native.source → ‖iteratedFDeriv ℝ j native z‖ ≤ NF j)
    (hInverse : ∀ j z, z ∈ native.target → ‖iteratedFDeriv ℝ j native.symm z‖ ≤ NI j)
    (hSource : ∀ z ∈ native.source,
      z.1 ∈ Ref.parameterNormDomain ip ∧ z.2 ∈ Ref.sourceNormDomain host)
    (Bp Bs : ℝ)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X)
    (hp : z.1 ∈ Ref.parameterNormDomain i.2) (hx : z.2 ∈ Ref.sourceNormDomain i.1)
    (hBp : ‖z.1‖ ≤ Bp) (hBs : ‖z.2‖ ≤ Bs) :
    let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart i.2) native
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
      (actualHostAdaptedChart (Ref.atlas.chart host) b)
    z ∈ t.source →
    ∀ j, ‖iteratedFDeriv ℝ j t z‖ ≤ repairEntranceOriginalForwardProfile Bp NF Parameter Spatial j ∧
      ‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤ repairEntranceOriginalInverseProfile Bp Bs NI Parameter Spatial j := by
  intro b t hz
  let C := (Ref.parameterChart ip).symm.trans (Ref.parameterChart i.2)
  let Q := C.prod (OpenPartialHomeomorph.refl D)
  let S := repairReferenceHostTransition («Ep» := Ep) (Ref.atlas.chart i.1) (Ref.atlas.chart host)
  have hS := repair_reference_host_transition_smooth («Ep» := Ep)
    (Ref.atlas.chart i.1) (Ref.atlas.chart host)
    (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem host)
  have hQ := entranceParameterTransition_smooth Ref hd ip i.2
  have hNative := actual_host_slice_geometry_inputs (Ref.atlas.chart host)
    (hd.atlas_smooth.chart_mem host) native _ slices data
  have hb := round3Parameter_cross_native_smooth (Ref.parameterChart ip) (Ref.parameterChart i.2)
    (hd.parameter_charts_smooth ip) (hd.parameter_charts_smooth i.2) native hNative.2.1 hNative.2.2.1
  have hbp : Round3ParameterChartPreserves b := round3ParameterChartPullback_preserves C native hNativePreserves
  have hzS : z ∈ S.source := ⟨mem_univ _,hz.1.2,hz.2.1.2⟩
  have hzB : S z ∈ b.source := hz.2.2
  have hn := (round3ParameterChartPullback_source C native (S z)).mp hzB
  have hnSource : (Q.symm (S z)) ∈ native.source := hn.2.1
  have hOwnSample := hSource _ hnSource
  have hInnerP : (Q.symm (S z)).1 ∈ Ref.parameterNormDomain ip := hOwnSample.1
  have hInnerX : (S z).2 ∈ Ref.sourceNormDomain host := hOwnSample.2
  have hQback (k : ℕ) (hk : 1 ≤ k) (y : X) (hy : y.1 ∈ Ref.parameterNormDomain i.2)
      (hyQ : y ∈ Q.target) : ‖iteratedFDeriv ℝ k Q.symm y‖ ≤ Parameter k :=
    transition.parameter i.2 ip k hk y hy hyQ
  have hQforw (k : ℕ) (hk : 1 ≤ k) (y : X) (hy : y.1 ∈ Ref.parameterNormDomain ip)
      (hyQ : y ∈ Q.source) : ‖iteratedFDeriv ℝ k Q y‖ ≤ Parameter k :=
    transition.parameter ip i.2 k hk y hy hyQ
  have hNativeOut : native (Q.symm (S z)) ∈ Q.source := hzB.2
  have hNativeOutP : (native (Q.symm (S z))).1 ∈ Ref.parameterNormDomain ip := by
    rw [hNativePreserves _ hnSource]
    exact hInnerP
  have hNativePoint : (C.symm (S z).1,(S z).2)=Q.symm (S z) := rfl
  have hForwardB (j : ℕ) (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j b (S z)‖ ≤
      repairEntranceConjugatedForwardProfile NF Parameter Parameter j := by
    exact repairEntrance_positive_parameter_conjugation_at NF Parameter Parameter hNF hParameter hParameter
      C native hNative.2.1 hQ.1 hQ.2 j hj (S z) hzB
      (fun k _ _ => hForward k _ hnSource)
      (fun k hk _ => hQforw k hk _ hNativeOutP hNativeOut)
      (fun k hk _ => hQback k hk _ hp hzB.1.1)
  have hwB : t z ∈ b.target := b.map_source hzB
  have hBInv : b.symm (t z)=S z := b.left_inv hzB
  have hwP : (t z).1=z.1 := hbp (S z) hzB
  have hInvNative := (round3ParameterChartPullback_target C native (t z)).mp hwB
  have hInvNativeSource : native.symm (Q.symm (t z)) ∈ native.source :=
    native.map_target hInvNative.2.1
  have hInvNativeQ : native.symm (Q.symm (t z)) ∈ Q.source := hwB.2.2
  have hInverseB (j : ℕ) (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j b.symm (t z)‖ ≤
      repairEntranceConjugatedForwardProfile NI Parameter Parameter j := by
    have hConjSource : t z ∈ (round3ParameterChartPullback C native.symm).source := by
      exact (round3ParameterChartPullback_source C native.symm (t z)).mpr hInvNative
    have hh := repairEntrance_positive_parameter_conjugation_at NI Parameter Parameter hNI hParameter hParameter
      C native.symm hNative.2.2.1 hQ.1 hQ.2 j hj (t z) hConjSource
      (fun k _ _ => hInverse k _ hInvNative.2.1)
      (fun k hk _ => hQforw k hk _ (hSource _ hInvNativeSource).1 hInvNativeQ)
      (fun k hk _ => hQback k hk _ (by rwa [hwP]) hwB.1)
    exact hh
  have hCF : ∀ j, 0 ≤ repairEntranceConjugatedForwardProfile NF Parameter Parameter j :=
    repairEntranceCompositionProfile_nonneg Parameter (repairEntranceCompositionProfile NF Parameter)
      hParameter (repairEntranceCompositionProfile_nonneg NF Parameter hNF hParameter)
  have hCI : ∀ j, 0 ≤ repairEntranceConjugatedForwardProfile NI Parameter Parameter j :=
    repairEntranceCompositionProfile_nonneg Parameter (repairEntranceCompositionProfile NI Parameter)
      hParameter (repairEntranceCompositionProfile_nonneg NI Parameter hNI hParameter)
  intro j
  by_cases hj : j=0
  · subst j
    simp only [repairEntranceOriginalForwardProfile,repairEntranceOriginalInverseProfile,ite_true,
      norm_iteratedFDeriv_zero]
    constructor
    · rw [Prod.norm_def,hwP]
      apply max_le (hBp.trans (le_max_left _ _))
      have hv := hForward 0 _ hnSource
      rw [norm_iteratedFDeriv_zero] at hv
      exact ((norm_snd_le (native (Q.symm (S z)))).trans hv).trans (le_max_right _ _)
    · rw [t.left_inv hz,Prod.norm_def]
      exact max_le_max hBp hBs
  · have hj1 : 1 ≤ j := by omega
    simp only [repairEntranceOriginalForwardProfile,repairEntranceOriginalInverseProfile,hj,ite_false]
    constructor
    · have hh := repairEntrance_positive_trans_chart_at Spatial
        (repairEntranceConjugatedForwardProfile NF Parameter Parameter) hSpatial hCF
        S b hS.1 hb.1 j hj1 z ⟨hzS,hzB⟩
        (fun k hk _ => transition.spatial i.1 host k hk z hx hzS)
        (fun k hk _ => hForwardB k hk)
      exact hh
    · have hTargetS : b.symm (t z) ∈ S.target := by rw [hBInv]; exact S.map_source hzS
      have hh := repairEntrance_positive_trans_chart_at
        (repairEntranceConjugatedForwardProfile NI Parameter Parameter) Spatial hCI hSpatial
        b.symm S.symm hb.2 hS.2 j hj1 (t z) ⟨hwB,hTargetS⟩
        (fun k hk _ => hInverseB k hk) (by
          intro k hk hkj
          rw [hBInv]
          exact transition.spatial host i.1 k hk (S z) hInnerX (S.map_source hzS))
      exact hh


theorem repairEntrance_original_piece_observer_jets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hNI : ∀ j, 0 ≤ NI j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (hForward : ∀ j z, z ∈ piece.native.source → ‖iteratedFDeriv ℝ j piece.native z‖ ≤ NF j)
    (hInverse : ∀ j z, z ∈ piece.native.target → ‖iteratedFDeriv ℝ j piece.native.symm z‖ ≤ NI j)
    (hSource : ∀ z ∈ piece.native.source,
      z.1 ∈ Ref.parameterNormDomain ip ∧ z.2 ∈ Ref.sourceNormDomain piece.host)
    (Bp Bs : ℝ)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X)
    (hp : z.1 ∈ Ref.parameterNormDomain i.2) (hx : z.2 ∈ Ref.sourceNormDomain i.1)
    (hBp : ‖z.1‖ ≤ Bp) (hBs : ‖z.2‖ ≤ Bs) :
    let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart i.2) piece.native
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
      (actualHostAdaptedChart (Ref.atlas.chart piece.host) b)
    z ∈ t.source →
    ∀ j, ‖iteratedFDeriv ℝ j t z‖ ≤ repairEntranceOriginalForwardProfile Bp NF Parameter Spatial j ∧
      ‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤ repairEntranceOriginalInverseProfile Bp Bs NI Parameter Spatial j := by
  exact repairEntrance_original_native_observer_jets Ref hd ip piece.host piece.native _ piece.slices piece.data
    (round3Parameter_primary_native_preserves_phase Ref hd ip nu W piece).1
    NF NI Parameter Spatial hNF hNI hParameter hSpatial transition hForward hInverse hSource Bp Bs i z hp hx hBp hBs

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_original_native_observer_jets
#print axioms GlobalEmbedding.Continuation.repairEntrance_original_piece_observer_jets
