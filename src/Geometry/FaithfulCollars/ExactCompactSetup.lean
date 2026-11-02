import FaithfulCollars.CompactRepairSetup

/-!
# Explicit raw and compact Setup profiles independent of ambient manifolds

These are the same constructions as the existential suppliers, with their
actual fixed profile formulas exposed.  This permits one primitive budget
to be selected before the types of both source and parameter manifolds.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.FaithfulCollars
section Raw
variable {E F M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace P] [T2Space P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]

theorem originalCompactRawPair_at_fixed_profiles
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP : ℕ → ℝ) (Ds Dp : ℕ) :
    let BS := originalRefinedRawProfile E RSrc bSrc hbSrc
    let BP := originalRefinedRawProfile F RPar (bPar/4) (by positivity)
    ∀ (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
        (gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (ι : Type*) [Fintype ι]
        (chart : ι → OpenPartialHomeomorph P F) (Q : ι → Set F)
        (W : ι → Set P) (K : Set P)
        (_gP : OriginalParameterNormBuffer chart Q W K RPar bPar),
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,F) ∞ P) →
      A.supportDegree ≤ Ds →
      (∀ i, tensorEnlargedSupportDegree W i ≤ Dp) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ TP j) →
      let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
      ∃ s : SourceCollarNovFamily A0 Omega RSrc bSrc hbSrc,
        let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
        AS.chart = A.chart ∧ AS.support = A.support ∧ AS.supportDegree = A.supportDegree ∧
        IsSmoothBufferedAtlas AS ∧ CompactSpace M ∧
        ∃ (AP : TensorBufferedChartFamily ι P F)
          (KS : Fin A.count → Set E) (KP : ι → Set F),
          AP.chart = chart ∧ AP.buffer = bPar/32 ∧
          (∀ i, IsCompact (KS i) ∧ KS i ⊆ Omega i) ∧
          (∀ i, IsCompact (KP i) ∧ KP i ⊆ Q i) ∧
          (∀ i, bufferedSamplingCoordinates AS i ⊆ KS i) ∧
          (∀ i, tensorLocalSamplingCoordinates AP i ⊆ KP i) ∧
          ∃ rawS : TensorRawCutoffPreparation AS BS TS Ds,
            ∃ rawP : TensorLocalRawPreparation AP K BP TP Dp,
              rawS.raw = originalRefinedRaw A0 Omega RSrc bSrc hbSrc s ∧
              rawP.enlarged = W ∧
              (∀ i, HasCompactSupport (rawS.raw i)) ∧
              (∀ i, HasCompactSupport (rawP.raw i)) := by
  dsimp only
  have hbPar' : 0 < bPar/4 := by positivity
  intro A Omega gS ι _ chart Q W K gP hA hChart hDs hDp hSTrans hPTrans
  let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
  have hA0 : IsSmoothBufferedAtlas A0 := ⟨hA.chart_mem, hA.support_subset⟩
  have hSample0 : ∀ i, bufferedSamplingCoordinates A0 i ⊆ Omega i := gS.original_sampling
  obtain ⟨s⟩ := sourceCollarNov_construct RSrc bSrc hbSrc A0 Omega le_rfl hSample0 gS.norm_radius
  let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
  let KS := sourceRefinedSamplingCarrier A0 Omega RSrc bSrc hbSrc s
  have hKS (i) : IsCompact (KS i) ∧ KS i ⊆ Omega i :=
    ⟨sourceRefinedSamplingCarrier_compact A0 Omega RSrc bSrc hbSrc s i,
      sourceRefinedSamplingCarrier_original A0 Omega RSrc bSrc hbSrc le_rfl s hSample0 i⟩
  have hSampleS : ∀ i, bufferedSamplingCoordinates AS i ⊆ KS i :=
    refinedWorkingAtlas_sampling_subset_carrier A0 Omega RSrc bSrc hbSrc le_rfl s
  let rawS := refinedRawPreparation A0 Omega RSrc bSrc hbSrc le_rfl s hA0
    gS.enlarged_buffer TS Ds hDs hSTrans
  let B0 := originalBufferedParameterSupportFamily chart Q W bPar hbPar gP.norm_target
  have hB0sample : ∀ i, tensorLocalSamplingCoordinates B0 i ⊆ Q i :=
    originalBufferedParameterSupportFamily_sampling chart Q W bPar hbPar gP.norm_target
  have hB0radius : ∀ i y, y ∈ tensorLocalInner B0 i → ‖y‖ ≤ RPar :=
    fun i y hy => gP.norm_radius i y (hB0sample i (tensorLocalInner_subset_sampling B0 i hy))
  obtain ⟨t⟩ := originalLocalBufferedCenters_construct RPar (bPar/4) hbPar' B0 hB0radius
  let AP := originalRefinedLocalFamily B0 RPar (bPar/4) hbPar' le_rfl t
  let KP := localRefinedSamplingCarrier RPar (bPar/4) hbPar' B0 t
  have hKP (i) : IsCompact (KP i) ∧ KP i ⊆ Q i :=
    ⟨localRefinedSamplingCarrier_compact RPar (bPar/4) hbPar' B0 t i,
      (localRefinedSamplingCarrier_sampling RPar (bPar/4) hbPar' B0 t le_rfl i).trans
        (hB0sample i)⟩
  have hSampleP : ∀ i, tensorLocalSamplingCoordinates AP i ⊆ KP i :=
    refinedLocalFamily_sampling_subset_carrier RPar (bPar/4) hbPar' B0 t le_rfl
  have hK : ∀ p ∈ K, ∃ i, p ∈ B0.inner i :=
    originalBufferedParameterFamily_cover chart (originalParameterSafeCoordinates chart Q W)
      bPar hbPar (fun i => inter_subset_left.trans (gP.norm_target i)) K gP.safe_ball_cover
  let rawP := localRefinedRawPreparation B0 W K RPar (bPar/4) hbPar' le_rfl t
    hChart hK (originalBufferedParameterSupportFamily_enlarged chart Q W bPar hbPar gP.norm_target)
    TP Dp hDp hPTrans
  refine ⟨s, rfl, rfl, rfl, refinedWorkingAtlas_smooth A0 Omega RSrc bSrc hbSrc
    le_rfl s hA0, sourceCompact_of_refined_carriers A0 Omega RSrc bSrc hbSrc le_rfl s
      hSample0 gS.norm_target, AP, KS, KP, rfl, ?_, hKS, hKP, hSampleS, hSampleP,
    rawS, rawP, rfl, rfl, ?_, ?_⟩
  · change (bPar/4)/8 = bPar/32
    ring
  · intro i
    apply compactSupport_of_internal_carrier (AS.chart i) (rawS.raw i) (KS i)
      (hKS i).1 ((hKS i).2.trans (gS.norm_target i))
    intro x hx
    have hi := rawS.inner_support i hx
    exact ⟨AS.inner_subset i hi, hSampleS i
      (bufferedInner_subset_sampling AS i (bufferedInnerCoordinates_mem AS i hi))⟩
  · intro i
    apply compactSupport_of_internal_carrier (AP.chart i) (rawP.raw i) (KP i)
      (hKP i).1 ((hKP i).2.trans (gP.norm_target i))
    intro p hp
    have hi := rawP.inner_support i hp
    exact ⟨AP.inner_subset i hi, hSampleP i
      (tensorLocalInner_subset_sampling AP i (tensorLocalInner_mem AP i hi))⟩

end Raw
section Setup
variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem originalCompactSetup_at_fixed_profiles
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    let BS := originalRefinedRawProfile Es RSrc bSrc hbSrc
    let BP := originalRefinedRawProfile Ep RPar (bPar/4) (by positivity)
    ∀ (A : BufferedAtlas M Es) (Omega : Fin A.count → Set Es)
        (gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (pc : ℕ) (chart : Fin pc → OpenPartialHomeomorph P Ep)
        (Q : Fin pc → Set Ep) (W : Fin pc → Set P),
      OriginalParameterNormBuffer chart Q W univ RPar bPar →
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P) →
      A.supportDegree ≤ Ds →
      (∀ i, tensorEnlargedSupportDegree W i ≤ Dp) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ TP j) →
      OriginalParameterJointTransitions (n := n) chart Q PT →
      OriginalSpatialJointTransitions (d := d) A Omega ST →
      ∃ g : SourceCollarNovSetup n d M P,
        ∃ hSourceCount : g.source.count = A.count,
          ∃ hParameterCount : g.parameter.count = pc,
          (∀ i, g.source.chart i = A.chart (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.chart i = chart (Fin.cast hParameterCount i)) ∧
          (∀ i, g.source.support i = A.support (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.support i ⊆ W (Fin.cast hParameterCount i)) ∧
          (∀ i, g.Omega i ⊆ Omega (Fin.cast hSourceCount i)) ∧
          (∀ i, g.Q i ⊆ Q (Fin.cast hParameterCount i)) ∧
          g.source.buffer = bSrc/8 ∧ g.parameter.buffer = bPar/32 ∧
          g.BS = BS ∧ g.BP = BP ∧ g.TS = TS ∧ g.TP = TP ∧
          g.parameterTransition = PT ∧ g.spatialTransition = ST ∧
          g.Ds = Ds ∧ g.Dp = Dp ∧
          g.coordinateRadius = max (max 0 RSrc) (max 0 RPar) := by
  dsimp only
  let BS := originalRefinedRawProfile Es RSrc bSrc hbSrc
  let BP := originalRefinedRawProfile Ep RPar (bPar/4) (by positivity)
  have hBS : ∀ j, 0 ≤ BS j := originalRefinedRawProfile_nonneg RSrc bSrc hbSrc
  have hBP : ∀ j, 0 ≤ BP j := originalRefinedRawProfile_nonneg RPar (bPar/4) (by positivity)
  have hPair := originalCompactRawPair_at_fixed_profiles
    (M := M) (P := P) (E := Es) (F := Ep) RSrc bSrc RPar bPar hbSrc hbPar TS TP Ds Dp
  intro A Omega gS pc chart Q W gP hA hChart hDs hDp hSTrans hPTrans hPJoint hSJoint
  obtain ⟨s, hASchart, hASsupport, hASdegree, hASsmooth, hMcompact,
    AP, KS, KP, hAPchart, hAPbuffer, hKS, hKP, hSampleS, hSampleP,
    rawS, rawP, hRawS, hRawP, hCompS, hCompP⟩ :=
    hPair A Omega gS (Fin pc) chart Q W univ gP hA hChart hDs hDp hSTrans hPTrans
  let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
  let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
  have hAPsmooth : ∀ i, AP.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hAPchart]
    exact hChart
  have hKSTarget : ∀ i, KS i ⊆ (AS.chart i).target :=
    fun i => (hKS i).2.trans (gS.norm_target i)
  have hKPTarget : ∀ i, KP i ⊆ (AP.chart i).target := by
    rw [hAPchart]
    exact fun i => (hKP i).2.trans (gP.norm_target i)
  let R := max (max 0 RSrc) (max 0 RPar)
  have hR : 0 ≤ R := (le_max_left 0 RSrc).trans (le_max_left _ _)
  have hSBound : ∀ i y, y ∈ KS i → ‖y‖ ≤ R := fun i y hy =>
    (gS.norm_radius i y ((hKS i).2 hy)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hPBound : ∀ i y, y ∈ KP i → ‖y‖ ≤ R := fun i y hy =>
    (gP.norm_radius i y ((hKP i).2 hy)).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hPJoint' : OriginalParameterJointTransitions (n := n) AP.chart KP PT := by
    rw [hAPchart]
    intro ip jp k hk z hz hsource
    exact hPJoint ip jp k hk z ((hKP ip).2 hz) hsource
  have hSJoint' : OriginalSpatialJointTransitions (d := d) AS KS ST := by
    intro i j k hk z hz hsource
    exact hSJoint i j k hk z ((hKS i).2 hz) hsource
  let g := compactSetupOfRawPair AS AP BS TS BP TP Ds Dp hBS hTS hBP hTP
    hASsmooth hAPsmooth rawS rawP KS KP (fun i => (hKS i).1) (fun i => (hKP i).1)
    hKSTarget hKPTarget hSampleS hSampleP R hR hSBound hPBound PT ST hPT hST hPJoint' hSJoint'
  refine ⟨g, rfl, rfl, (fun _ => rfl), ?_, (fun _ => rfl), ?_,
    (fun i => (hKS i).2), (fun i => (hKP i).2), rfl, hAPbuffer,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i
    exact congrFun hAPchart i
  · intro i p hp
    have h : p ∈ rawP.enlarged i := hp.1
    rwa [hRawP] at h

end Setup
end GlobalEmbedding.Continuation.FaithfulCollars
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.originalCompactRawPair_at_fixed_profiles
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.originalCompactSetup_at_fixed_profiles
