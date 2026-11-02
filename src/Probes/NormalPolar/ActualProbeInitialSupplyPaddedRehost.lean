import NormalPolar.ActualProbeInitialSupplySignedRehost
import NormalPolar.JointSecondarySignedNativeProfiles
import Probes.ActualFinalHostRawProfiles

/-! The actual extra-host background is restricted to exactly the source
and inverse-image sample of the same padded signed secondary choice. Empty
entries retain the genuine empty source. No additional host or sampling
certificate is supplied by the caller. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P Tr Β Rec : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Β] [Fintype Rec] [DecidableEq Rec]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem actualProbeInitialSupply_padded_rehost_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hQ : IsCompact (Data.parameterNormDomain i.2))
    (hOmega : IsCompact (Data.sourceNormDomain i.1))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (phase : Rec → M → ℝ) (K O : Rec → Set M)
    (seeds : (rec : Rec) → JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (phase rec) (K rec) (O rec))
    (s : Σ rec, Fin (seeds rec).refinement.count) :
    let B := Data.parameterChart i.2
    let Q := Data.parameterNormDomain i.2
    let hQT := hd.parameter_norm_subset i.2
    let Spatial := passiveOriginalSpatialNormSample Data i.1
    let W := round3ParameterNativeDomain B (univ : Set (P × M))
    let Sold := (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i
    ∃ C : ℕ → ℕ → ℝ → ℝ, ∃ Tgeo : ℕ → ℝ,
      (∀ k, 0 ≤ Tgeo k) ∧ (∀ n j B, 0 ≤ B → 0 ≤ C n j B) ∧
      ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
        (nG jG n length j Rsub Lprimary : ℕ)
        (reserve Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd)
        (Tbackground : ℕ → ℝ) (hTbackground : ∀ k, 0 ≤ Tbackground k)
        (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N)
          (Λ := Fin Data.primaryCount) (Β := Β) (fun _ : Ep => scale • F0)),
        (∀ nu, g.cutoff nu = fun z => Data.cutoff nu (B.symm z.1,z.2)) →
        (∀ nu, g.phase nu = fun z => Data.phase nu (B.symm z.1,z.2)) →
        ∀ (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
        (primary : Fin Data.primaryCount → Set (Ep × M))
        (Oold : Set X) (tau ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1),
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
          reserve Bnd Mg Tbackground (fun _ : Ep => scale • F0)
          (fun _ => contMDiff_const_rescale F0 hF0 scale) g input input W primary
          (Data.atlas.chart i.1) Oold Sold tau ell 0 →
        ∀ rec, Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
          reserve (C n j Bnd) Mg
          (fun k => actualFastChartTransferPrefix Tgeo k*bufferedTransitionPrefix Tbackground k)
          (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
          g input input W primary (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
          (jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).source
          ((jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).symm ''
            (jointSecondarySignedNativeRaw seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).sample)
          tau ell 0) := by
  intro B Q hQT Spatial W Sold
  obtain ⟨C,Tgeo,hTgeo,hC,hProduce⟩ := actualProbeInitialSupply_signed_rehost_uniform
    (Tr := Tr) (Β := Β) Data hd hs hAll i hQ hOmega
    ((seeds s.1).inner s.2) ((seeds s.1).outer s.2) ((seeds s.1).nested s.2)
  refine ⟨C,Tgeo,hTgeo,hC,?_⟩
  intro scale hscale nG jG n length j Rsub Lprimary reserve Bnd Mg hBnd
    Tbackground hTbackground g hCutoff hPhase input primary Oold tau ell hell hell1 raw rec
  obtain ⟨full⟩ := hProduce n length j Rsub Lprimary reserve Bnd Mg hBnd Tbackground hTbackground
    (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
    g hCutoff hPhase input primary Oold tau ell raw
  let host := (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
  let geom := jointSecondarySignedNativeRaw seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s
  let tr := jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s
  let R := Q ×ˢ ((seeds s.1).inner s.2).adaptedActiveSample Spatial
  have hh : host = ((seeds s.1).outer s.2).chart := jointSecondarySeedPaddedChoice_host seeds rec s
  have hDomain : tr.source ⊆ actualRawObserverOpen ((seeds s.1).outer s.2).chart W := by
    intro z hz
    have ht := jointSecondarySignedNativeHost_source seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s hz
    rw [jointSecondarySeedPaddedChoice_host] at ht
    exact ⟨⟨mem_univ _,ht.2⟩,ht.1,mem_univ _⟩
  have hSamples : tr.symm '' geom.sample ⊆ R := by
    change (jointSecondarySignedNativeHostTransition seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).symm ''
      (jointSecondarySignedNativeRaw seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s).sample ⊆ R
    rw [jointSecondarySignedNativeHost_sample]
    by_cases h : s.1 = rec
    · simpa only [jointSecondarySignedNativeSample,if_pos h] using (Subset.rfl : R ⊆ R)
    · simp only [jointSecondarySignedNativeSample,if_neg h]
      exact empty_subset _
  exact actual_final_host_raw_profiles n length j Rsub Lprimary reserve (C n j Bnd) Mg
    (fun k => actualFastChartTransferPrefix Tgeo k*bufferedTransitionPrefix Tbackground k)
    (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
    g input input W primary (fun _ : Unit => ((seeds s.1).outer s.2).chart)
    (fun _ => actualRawObserverOpen ((seeds s.1).outer s.2).chart W) (fun _ => R)
    tau ell 0 (fun _ => full) () host hh geom.chart geom.sample
    (jointSecondarySignedNativeRaw_host_source seeds B Q hQT Spatial scale hscale nG jG ell hell hell1 rec s)
    geom.sample_subset hDomain hSamples

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_padded_rehost_uniform
