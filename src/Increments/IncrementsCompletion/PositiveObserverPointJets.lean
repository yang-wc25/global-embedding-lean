import IncrementsCompletion.PositiveObserverJets

/-!
# Original observer bounds from native jets at the one actual host point

No estimate on the whole native chart source or target is needed.  The
forward jets are read only at the original host coordinates of the actual
observer sample; inverse jets are read only at its native image.  Those
points are preserved literally through the conjugation and its inverse.
This permits original sample-based phase/inverse producers to feed the
observer estimate without enlarging their original norm domains.
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

/-- Literal original host coordinates of the original observer point. -/
def incrementsCompletionOriginalHostPoint
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Ref.parameterCount) (host : Fin Ref.atlas.count)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X) : X :=
  (Ref.parameterChart ip ((Ref.parameterChart i.2).symm z.1),
    Ref.atlas.chart host ((Ref.atlas.chart i.1).symm z.2))

private theorem incrementsCompletionPointParameterTransition_smooth
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

theorem incrementsCompletion_original_native_observer_point_jets_at
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (host : Fin Ref.atlas.count)
    (native : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (slices : Ep → OpenPartialHomeomorph M D)
    (data : ActualOriginalHostSliceData (Ref.atlas.chart host) native psi slices)
    (hNativePreserves : Round3ParameterChartPreserves native)
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ j, 1 ≤ j → 0 ≤ NF j) (hNI : ∀ j, 1 ≤ j → 0 ≤ NI j)
    (hParameter : ∀ j, 1 ≤ j → 0 ≤ Parameter j) (hSpatial : ∀ j, 1 ≤ j → 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (z : X)
    (hp : z.1 ∈ Ref.parameterNormDomain i.2) (hx : z.2 ∈ Ref.sourceNormDomain i.1)
    (hOwnP : Ref.parameterChart ip ((Ref.parameterChart i.2).symm z.1) ∈ Ref.parameterNormDomain ip)
    (hOwnX : Ref.atlas.chart host ((Ref.atlas.chart i.1).symm z.2) ∈ Ref.sourceNormDomain host)
    (hForward : ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j native (incrementsCompletionOriginalHostPoint Ref ip host i z)‖ ≤ NF j)
    (hInverse : ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j native.symm (native (incrementsCompletionOriginalHostPoint Ref ip host i z))‖ ≤ NI j) :
    let b := round3ParameterCrossNativeChart (Ref.parameterChart ip) (Ref.parameterChart i.2) native
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
      (actualHostAdaptedChart (Ref.atlas.chart host) b)
    z ∈ t.source → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j t z‖ ≤ incrementsCompletionPositiveObserverForwardProfile NF Parameter Spatial j ∧
      ‖iteratedFDeriv ℝ j t.symm (t z)‖ ≤ incrementsCompletionPositiveObserverInverseProfile NI Parameter Spatial j := by
  intro b t hz
  let C := (Ref.parameterChart ip).symm.trans (Ref.parameterChart i.2)
  let Q := C.prod (OpenPartialHomeomorph.refl D)
  let S := repairReferenceHostTransition («Ep» := Ep) (Ref.atlas.chart i.1) (Ref.atlas.chart host)
  have hS := repair_reference_host_transition_smooth («Ep» := Ep)
    (Ref.atlas.chart i.1) (Ref.atlas.chart host)
    (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem host)
  have hQ := incrementsCompletionPointParameterTransition_smooth Ref hd ip i.2
  have hNative := actual_host_slice_geometry_inputs (Ref.atlas.chart host)
    (hd.atlas_smooth.chart_mem host) native _ slices data
  have hb := round3Parameter_cross_native_smooth (Ref.parameterChart ip) (Ref.parameterChart i.2)
    (hd.parameter_charts_smooth ip) (hd.parameter_charts_smooth i.2) native hNative.2.1 hNative.2.2.1
  have hbp : Round3ParameterChartPreserves b := round3ParameterChartPullback_preserves C native hNativePreserves
  have hzS : z ∈ S.source := ⟨mem_univ _,hz.1.2,hz.2.1.2⟩
  have hzB : S z ∈ b.source := hz.2.2
  have hn := (round3ParameterChartPullback_source C native (S z)).mp hzB
  have hnSource : Q.symm (S z) ∈ native.source := hn.2.1
  have hPoint : Q.symm (S z) = incrementsCompletionOriginalHostPoint Ref ip host i z := rfl
  have hInnerP : (Q.symm (S z)).1 ∈ Ref.parameterNormDomain ip := hOwnP
  have hInnerX : (S z).2 ∈ Ref.sourceNormDomain host := hOwnX
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
  have hForwardB (j : ℕ) (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j b (S z)‖ ≤
      incrementsCompletionPositiveConjugationProfile NF Parameter Parameter j := by
    exact incrementsCompletion_positive_parameter_conjugation_at NF Parameter Parameter hNF hParameter hParameter
      C native hNative.2.1 hQ.1 hQ.2 j hj (S z) hzB (by
        intro k hk hkj
        change ‖iteratedFDeriv ℝ k native (Q.symm (S z))‖ ≤ NF k
        rw [hPoint]
        exact hForward k hk)
      (fun k hk _ => hQforw k hk _ hNativeOutP hNativeOut)
      (fun k hk _ => hQback k hk _ hp hzB.1.1)
  have hwB : t z ∈ b.target := b.map_source hzB
  have hBInv : b.symm (t z)=S z := b.left_inv hzB
  have hwP : (t z).1=z.1 := hbp (S z) hzB
  have hInvNative := (round3ParameterChartPullback_target C native (t z)).mp hwB
  have hInvNativeQ : native.symm (Q.symm (t z)) ∈ Q.source := hwB.2.2
  have hNativeOutEq : Q.symm (t z) = native (Q.symm (S z)) := Q.left_inv hNativeOut
  have hInvPoint : native.symm (Q.symm (t z)) = Q.symm (S z) := by
    rw [hNativeOutEq,native.left_inv hnSource]
  have hInverseB (j : ℕ) (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j b.symm (t z)‖ ≤
      incrementsCompletionPositiveConjugationProfile NI Parameter Parameter j := by
    have hConjSource : t z ∈ (round3ParameterChartPullback C native.symm).source := by
      exact (round3ParameterChartPullback_source C native.symm (t z)).mpr hInvNative
    exact incrementsCompletion_positive_parameter_conjugation_at NI Parameter Parameter hNI hParameter hParameter
      C native.symm hNative.2.2.1 hQ.1 hQ.2 j hj (t z) hConjSource (by
        intro k hk hkj
        change ‖iteratedFDeriv ℝ k native.symm (Q.symm (t z))‖ ≤ NI k
        rw [hNativeOutEq,hPoint]
        exact hInverse k hk)
      (fun k hk _ => hQforw k hk _ (by
        change (native.symm (Q.symm (t z))).1 ∈ Ref.parameterNormDomain ip
        rw [hInvPoint]
        exact hInnerP) hInvNativeQ)
      (fun k hk _ => hQback k hk _ (by rwa [hwP]) hwB.1)
  have hCF : ∀ j, 0 ≤ incrementsCompletionPositiveConjugationProfile NF Parameter Parameter j :=
    incrementsCompletionPositiveConjugationProfile_nonneg NF Parameter Parameter hNF hParameter hParameter
  have hCI : ∀ j, 0 ≤ incrementsCompletionPositiveConjugationProfile NI Parameter Parameter j :=
    incrementsCompletionPositiveConjugationProfile_nonneg NI Parameter Parameter hNI hParameter hParameter
  intro j hj
  constructor
  · exact incrementsCompletion_positive_trans_chart_at Spatial
      (incrementsCompletionPositiveConjugationProfile NF Parameter Parameter) hSpatial (fun k _ => hCF k)
      S b hS.1 hb.1 j hj z ⟨hzS,hzB⟩
      (fun k hk _ => transition.spatial i.1 host k hk z hx hzS)
      (fun k hk _ => hForwardB k hk)
  · have hTargetS : b.symm (t z) ∈ S.target := by rw [hBInv]; exact S.map_source hzS
    exact incrementsCompletion_positive_trans_chart_at
      (incrementsCompletionPositiveConjugationProfile NI Parameter Parameter) Spatial (fun k _ => hCI k) hSpatial
      b.symm S.symm hb.2 hS.2 j hj (t z) ⟨hwB,hTargetS⟩
      (fun k hk _ => hInverseB k hk) (by
        intro k hk hkj
        rw [hBInv]
        exact transition.spatial host i.1 k hk (S z) hInnerX (S.map_source hzS))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_native_observer_point_jets_at
