import NormalPolar.JointSecondaryPrescribedNativeHost
import NormalPolar.JointSecondarySignedHostSamples

/-! The actual original wave family supplies prescribed primitive profiles
on every host of the same signed secondary family. Compact samples, host
maximality, source inclusion and actual inverse-image sample inclusion are
all proved from the constructed signed seeds. No extra observation budget
or prepared prescribed profile is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N r : ℕ} {M Obs Rec P Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [Fintype Obs] [Fintype Rec] [DecidableEq Rec]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
  {phase : Rec → M → ℝ} {K O : Rec → Set M}

theorem jointSecondary_signed_prescribed_from_original_waves
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (seeds : (rec : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (phase rec) (K rec) (O rec))
    (S : Obs → Set M) (hS : ∀ i, IsCompact (S i)) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) (nG jG nP jP : ℕ) (ell : ℝ)
      (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (i : Obs) (B : OpenPartialHomeomorph P Ep)
      (Q : Set Ep) (hQ : Q ⊆ B.target) (rec : Rec)
      (s : Σ rec, Fin (seeds rec).refinement.count),
      Nonempty (JointGroupedPrescribedObservationProfiles
        (fun _ : Ep => c • F) (fun _ => contMDiff_const_rescale F hF c)
        (fun l a _ => (family.outer l a).spatialChart.symm)
        (fun l a (z : X) => (family.refinement l).cutoffCoordinates a (0,z.2))
        (fun l a _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
          ((family.outer l a).spatialChart.symm x)
          ((waves l).normal ((family.outer l a).spatialChart.symm x)))
        (fun l a => round3ParameterChartPullback B
          (passiveParameterChart (0 : Z) (family.inner l a).chart))
        {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ (univ : Set (Z × M))}
        (fun l a => {z : Ep × M | z.1 ∈ B.target ∧
          (0,z.2) ∈ tsupport ((family.refinement l).cutoff a)})
        nP jP ell (family.geometryBudget (max nP jP)) (family.cutoffBudget nP) (family.normalBudget nP)
        (fun z : X => (z.1,(jointSecondarySeedPaddedChoice (P := P) seeds rec s).host.symm z.2))
        (jointSecondarySignedNativeHostTransition seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s).source
        ((jointSecondarySignedNativeHostTransition seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s).symm ''
          (jointSecondarySignedNativeRaw seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s).sample)
        T (fun l z => weight l * (waves l).phase z.2) (Pphase jP)) := by
  let Idx := Obs × ((rec : Rec) × Fin (seeds rec).refinement.count)
  let host (idx : Idx) := ((seeds idx.2.1).outer idx.2.2).chart
  let R (idx : Idx) := ((seeds idx.2.1).inner idx.2.2).adaptedActiveSample (S idx.1)
  have hh (idx : Idx) : host idx ∈ maximalAtlas IM ∞ M := ((seeds idx.2.1).outer idx.2.2).maximal
  have hR (idx : Idx) : IsCompact (R idx) :=
    ((seeds idx.2.1).inner idx.2.2).adaptedActiveSample_compact (S idx.1) (hS idx.1)
  have hRt (idx : Idx) : R idx ⊆ (host idx).target :=
    jointSecondarySignedNativeHost_spatial_target seeds (S idx.1) idx.2
  obtain ⟨T,Pphase,hpos,hprofiles⟩ := jointSecondary_prescribed_finite_native_host_profiles
    (P := P) (Ep := Ep) family host hh R hR hRt
  refine ⟨T,Pphase,hpos,?_⟩
  intro c hc nG jG nP jP ell hell hell1 i B Q hQ rec s
  let tr := jointSecondarySignedNativeHostTransition seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s
  let Sn := tr.symm '' (jointSecondarySignedNativeRaw seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s).sample
  have hOmega : tr.source ⊆ B.target ×ˢ (host ⟨i,s⟩).target := by
    simpa only [jointSecondarySeedPaddedChoice_host] using
      jointSecondarySignedNativeHost_source seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s
  have hSn : Sn ⊆ B.target ×ˢ R ⟨i,s⟩ :=
    jointSecondarySignedNativeHost_sample_subset seeds B Q hQ (S i) c hc nG jG ell hell hell1 rec s
  have out := hprofiles c hc nP jP ell hell hell1 ⟨i,s⟩ B tr.source Sn hOmega
    (fun _ hz => (hSn hz).1) (fun _ hz => (hSn hz).2)
  simpa only [jointSecondarySeedPaddedChoice_host] using out

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_signed_prescribed_from_original_waves
