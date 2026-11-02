import UpgradeContinuation.OriginalReferenceSupply
import ProbesClosure.GeneralBackgroundSelectedSharp
import UpgradeContinuation.GeneralOriginalSelectedQ440
import NormalPolar.PassiveOriginalRescaledPhysical
import NormalPolar.PassiveRawRecenter

/-!
# The same selected general-cutoff source supplies the actual sharp background

The primary reserve supplier retained by the same initialized q440 choice
is recentered at the actual nearby target.  The actual physical geometry
is manufactured from the same original primary packet.  Consequently the
sharp background endpoint no longer asks for a canonical supplier or a
completed geometry record at each target.  The original rho, Tp, Pphase,
initialized atlas, labels, and full parameter ball are unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
open scoped ContDiff Topology Classical ENNReal

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N r : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

/-- The actual original primary packet removes both the targetwise raw
supplier and the physical-geometry premises from the selected-source sharp
background endpoint.  All constants are fixed before scale, ell, or H. -/
theorem generalReference_selected_background_sharp
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep)
    (hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (Tp Pphase : ℕ → ℝ) (hTp : ∀ k, 0 < Tp k ∧ 0 < Pphase k)
    (numbers : Round3RepairMeanPrimitiveProfiles) (rho : ℝ) (hrho : 0 < rho)
    (hrhoEq : rho = numbers.rho/2) :
    let A := s.seed.atlas
    let Samples := incrementsOriginalEvaluation A B.chart s.seed.sourceNormDomain Q univ
    ∀ (hSamples : ∀ i, IsCompact (Samples i)),
    let hDomain : ∀ i, Samples i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
    let Data := passiveOriginalData (0 : Z) s.seed B Q
    let g0 := passiveOriginalReferencePrimary s.seed s.domain s.smooth s.freeNormal
      s.baseIndex s.refinementMultiplicity s.primary
    let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => s.seed.F (p,x)) g0
    ProbesSelectedPrimarySupplier A B Samples hSamples hDomain F0 hF0 gp Data.primaryDomain Data.H numbers →
    ProbesSelectedGeneralProfiles F0 hF0 waves weight family A B Samples Tp Pphase →
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
    ∀ HBound : ℕ → ℝ, ∃ cap C : ℝ, 0 < cap ∧ 0 ≤ C ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2 : ℝ) 1)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H0 H : parameterRound2_originalTensorGermSpace A B.chart Samples univ),
    H0.val = Data.H →
    parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell 0 (H-H0) ≤ rho →
    (∀ j, parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell j H ≤ HBound j) →
    let F := fun _ : Z => scale • F0
    let hF := fun _ : Z => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : Z => F0) (fun _ => hF0) g0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    ∀ (target : (z : Z) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x)),
    H.val = (fun _ : P => target 0) →
    ∀ (label : (Fin r × Bool) ↪ Fin d) (epsilon : ℝ), 0 < epsilon → epsilon < cap →
    ∀ (delta : ℝ), 0 < delta →
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z → D → M :=
      fun l a (_ : Z) => ((family.piece l).seed.outer a).chart.symm
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z × D → ℝ :=
      fun l a (z : Z × D) => (family.piece l).seed.cutoffCoordinates a (0,z.2)
    let nu : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l a z x) := fun l a (_ : Z) x => actualRescaledNormal F0 hF0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) (((family.piece l).seed.outer a).chart.symm x)
      ((waves l).normal (((family.piece l).seed.outer a).chart.symm x))
    let charts : (l : Fin r) → Fin (family.piece l).seed.refinement.count →
        OpenPartialHomeomorph (Z × M) (Z × D) := fun l a => (family.piece l).seed.physicalChart a
    let phase : Fin r → Z × M → ℝ := fun l (z : Z × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l a z x) :=
      fun l a z x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l a (z,x) • nu l a z x)
    let probe := jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase (epsilon*ell) 442 charts
    ProbesBackgroundNativeSharp A Initialized Samples b (epsilon*ell) C
      (jointMixedSeedBackgroundWave (0 : Z) F hF g 442 (epsilon*ell) delta target probe 441) := by
  intro A Samples hSamples hDomain Data g0 gp hPrimary hProfiles
    Mgp Bchi Bnu Mphase Csrc Initialized HBound
  have hSQ i z (hz : parameterTensorModelEquiv (m+1) d z ∈ Samples i) : z.1 ∈ Q i.2 := by
    have he := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 at he
    simpa only [he] using hz.2.2.1
  have hSR i z (hz : parameterTensorModelEquiv (m+1) d z ∈ Samples i) :
      z.2 ∈ s.seed.sourceNormDomain i.1 := by
    have he := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at he
    simpa only [he] using hz.2.1
  obtain ⟨Ku,hKu,hKu0,hsharp⟩ := probes_background_sharp_of_selected_general_profiles
    (Tr := ℝ) (Λ := Fin s.seed.primaryCount) (Β := s.subdivisionIndex)
    F0 hF0 waves weight family A s.domain.atlas_smooth s.seed.sourceNormDomain
    s.fixed.source_compact s.domain.source_norm_subset B hB Q
    (fun i => (hQ i).1) (fun i => (hQ i).2.1)
    Samples hSamples hDomain hSQ hSR 440 (by norm_num) rho hrho b p₀ hp₀ Tp Pphase hTp hProfiles
  obtain ⟨cap,C,hcap,hC,hsharp⟩ := hsharp HBound numbers.Rsub numbers.Lprimary
    numbers.reserve numbers.reserve_pos numbers.Bnd numbers.Mg numbers.Dinput
    numbers.Bnd_nonneg numbers.Mg_nonneg numbers.Dinput_nonneg numbers.T numbers.T_nonneg
  refine ⟨cap,C,hcap,hC,?_⟩
  intro scale hscale ell hell hell1 H0 H hH0 hCenter hH F hF g target hTarget
    label epsilon hepsilon hecap delta hdelta c chi nu charts phase vf probe
  let pnorm := parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell
  have hBase := hPrimary scale hscale ell hell hell1 H0 hH0
  have hRecenter := round3Parameter_canonical_supply_recenter A B.chart Samples univ pnorm
    H0 H numbers.rho 440 numbers.Rsub numbers.Lprimary numbers.reserve
    numbers.Bnd numbers.Mg numbers.Dinput numbers.T
    (fun _ : P => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
    (passiveRescaledPrimary (fun _ : P => F0) (fun _ => hF0) gp scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)) Data.primaryDomain ell hBase
    (by simpa only [← hrhoEq] using hCenter)
  rw [← hrhoEq] at hRecenter
  have hzero : (0 : Z) ∈ s.seed.parameterOpen := s.domain.parameter_subset (by rw [s.parameterSet_eq]; trivial)
  have hInner (i) (p : P) (hp : p ∈ B.inner i) : B.chart i p ∈ Q i :=
    (hQ i).2.2 (subset_closure (bufferedInner_subset_sampling B i (bufferedInnerCoordinates_mem B i hp)))
  let hd := passiveOriginalData_domain (0 : Z) s.seed s.domain hzero B hB Q
    (fun i => (hQ i).2.1) hInner
  have hb0 : (0 : Z) ∈ (s.seed.parameterChart s.baseIndex.2).target := by
    rw [s.parameter_identity]
    trivial
  let hs := passiveOriginalData_smooth (0 : Z) s.seed s.smooth hzero s.baseIndex.2 hb0 B Q
  have hGeometry := passiveOriginal_reference_rescaled_physical_geometry
    s.seed s.domain s.smooth s.freeNormal s.immersion s.parameterSet_eq
    s.baseIndex s.parameter_identity s.refinementMultiplicity s.primary
    B hB Q hSamples hd hs scale hscale.1
  exact hsharp scale hscale ell hell hell1 H hH g target hTarget Data.primaryDomain hRecenter
    label epsilon hepsilon hecap delta hdelta (fun i => Classical.choice (hGeometry (i,b)))

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalReference_selected_background_sharp
