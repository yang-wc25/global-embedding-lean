import NormalPolar.ActualProbeInitialSupplyRehostRaw
import NormalPolar.PassiveOriginalObserverNormSamples
import Probes.ActualRelativeInteractionCarrier
import Probes.Round3ParameterRawAtlasData

/-! Actual signed buffers rehost the same background on the original norm
samples.  Original smooth phase data manufacture the phase-gradient budget;
the true compact active image manufactures the overlap and sampling maps.
Only literal primitive identities with the original cutoff and phase are
used.  No extra-host profile, completed estimate or new norm is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Tr Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable {phase : M → ℝ} {K O : Set M}
  {ref : JointSecondarySignedRefinement (m := m) phase K O} {ib : Fin ref.count}

theorem actualProbeInitialSupply_signed_rehost_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hQ : IsCompact (Data.parameterNormDomain i.2))
    (hOmega : IsCompact (Data.sourceNormDomain i.1))
    (b b' : JointSecondarySignedBuffer ref ib)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget) :
    let W := round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))
    let R := Data.parameterNormDomain i.2 ×ˢ
      b.adaptedActiveSample (passiveOriginalSpatialNormSample Data i.1)
    let S := (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i
    ∃ C : ℕ → ℕ → ℝ → ℝ, ∃ Tgeo : ℕ → ℝ,
      (∀ k, 0 ≤ Tgeo k) ∧ (∀ n j B, 0 ≤ B → 0 ≤ C n j B) ∧
      ∀ (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd)
        (Tbackground : ℕ → ℝ) (hTbackground : ∀ k, 0 ≤ Tbackground k)
        (F : Ep → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
        (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N)
          (Λ := Fin Data.primaryCount) (Β := Β) F),
        (∀ nu, g.cutoff nu = fun z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)) →
        (∀ nu, g.phase nu = fun z => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) →
        ∀ (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
        (primary : Fin Data.primaryCount → Set (Ep × M))
        (Oold : Set X) (tau ell : ℝ),
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
          reserve Bnd Mg Tbackground F hF g input input W primary
          (Data.atlas.chart i.1) Oold S tau ell 0 →
        Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
          reserve (C n j Bnd) Mg
          (fun k => actualFastChartTransferPrefix Tgeo k*bufferedTransitionPrefix Tbackground k)
          F hF g input input W primary b'.chart (actualRawObserverOpen b'.chart W) R tau ell 0) := by
  intro W R S
  have hSample := passiveOriginal_signed_full_norm_samples Data hd hAll i hQ hOmega b b' hbb
  have hOverlap : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep)
      (Data.atlas.chart i.1) b'.chart := by
    intro z hz
    exact ⟨mem_univ _,(hSample.2.1 hz).2⟩
  have hSpatial := passiveOriginal_spatial_norm_sample Data hd i.1 hOmega
  obtain ⟨Ph,hPh,hPhFields⟩ := passiveOriginal_signed_observer_fields Data hd hs hAll i b b' hbb
    (Data.parameterNormDomain i.2) hQ (Subset.rfl)
    (passiveOriginalSpatialNormSample Data i.1) hSpatial.1 hSpatial.2.1
    (fun z hz => hSpatial.2.2 ▸ hz)
  obtain ⟨C,Tgeo,hTgeo,hC,hRehost⟩ := actualProbeInitialSupply_raw_rehost_uniform
    (N := N) (Λ := Fin Data.primaryCount) (Β := Β)
    (Data.atlas.chart i.1) b'.chart (hd.atlas_smooth.chart_mem i.1) b'.maximal
    R hSample.1 hOverlap
  refine ⟨fun n j B => C j (actualProbeRawScalarCost n j B) (Ph j),Tgeo,hTgeo,
    fun n j B hB => hC j _ _ (actualProbeRawScalarCost_nonneg n j B hB) (hPh j),?_⟩
  intro n length j Rsub Lprimary reserve Bnd Mg hBnd Tbackground hTbackground F hF g
    hCutoff hPhase input primary Oold tau ell raw
  let scalar := actualProbeInitialSupply_raw_scalarize n length j Rsub Lprimary reserve Bnd Mg hBnd
    Tbackground F hF g input input W primary (Data.atlas.chart i.1) Oold S tau ell 0 raw
  apply hRehost n length j Rsub Lprimary reserve (actualProbeRawScalarCost n j Bnd) Mg
    (actualProbeRawScalarCost_nonneg n j Bnd hBnd) Tbackground hTbackground F hF g input
    W primary Oold S tau ell scalar hSample.2.2 (Ph j) (hPh j)
  intro nu r k hk z hz hActive
  let pull : Ep × M → P × M := fun w => ((Data.parameterChart i.2).symm w.1,w.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
      (fun _ hw => hw.1)).prodMk continuous_snd.continuousOn
  have hPullSupport := actual_relative_support_pullback_subset W (incrementsOriginalParameterRegion Data)
    pull hPull (fun _ _ => ⟨hd.parameter_subset (by rw [hAll]; exact mem_univ _),mem_univ _⟩)
    (Data.cutoff nu)
  rw [hCutoff nu] at hActive
  have hOriginal : pull (z.1,b'.chart.symm z.2) ∈
      incrementsOriginalRelativeCutoffSupport Data nu :=
    hPullSupport hActive
  rw [parameterRound2_original_relativeSupport_eq Data hd.parameter_open] at hOriginal
  have hzField : z ∈ passiveOriginalSignedObserverSample Data nu i b b'
      (Data.parameterNormDomain i.2) (passiveOriginalSpatialNormSample Data i.1) :=
    ⟨hz,hOriginal.2⟩
  have hb := (hPhFields ell (raw.htau.trans_le raw.htaul).le raw.hell1 nu j k hk z hzField).2.2 r
  simpa only [hPhase nu] using hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_signed_rehost_uniform
