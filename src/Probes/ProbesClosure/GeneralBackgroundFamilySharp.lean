import ProbesClosure.BackgroundFamilySharp
import ProbesClosure.GeneralParameterProfiles
import NormalPolar.PassiveOriginalSmallParameter

/-!
# Actual arbitrary-cutoff wave families supply their sharp background responses

The original finite subordinate pieces manufacture every primitive source
profile. Their chosen transition and phase costs also fix the amplitude and
the actual global parameter. The same costs are then used for the fixed
forcing and the moving forcing, before every contraction and small scale.
This is the source-producing version of `BackgroundGroupedSharp`; no raw
profile, forcing germ, parameter jet budget, jointness or response is an
input. The original canonical primary reserve supplier is still explicit,
so this declaration is an integration component, not the original probes
existence theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
universe uM uP uTr uL uB
variable {m N p r : ℕ} {M : Type uM} {P : Type uP}
  {Tr : Type uTr} {Λ : Type uL} {Β : Type uB}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => Fin p → ℝ
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The finite actual original wave family and the fixed original samples
manufacture all source and global-parameter profiles needed by the sharp
background constructor. Every cost precedes the contraction and scales. -/
theorem probes_background_sharp_of_general_family
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F0 hF0)
    (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (R : Fin A.count → Set D) (hR : ∀ i, IsCompact (R i))
    (hRt : ∀ i, R i ⊆ (A.chart i).target)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+p) → ℝ))
    (hSamples : ∀ i, IsCompact (Samples i))
    (hDomain : ∀ i, Samples i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (hSQ : ∀ i z, parameterTensorModelEquiv (m+1) p z ∈ Samples i → z.1 ∈ Q i.2)
    (hSR : ∀ i z, parameterTensorModelEquiv (m+1) p z ∈ Samples i → z.2 ∈ R i.1)
    (q : ℕ) (hq : 1 ≤ q) (rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ∃ Tp Pphase : ℕ → ℝ, (∀ k, 0 < Tp k ∧ 0 < Pphase k) ∧
    let Mgp := fun j => family.geometryBudget (max (j+(q+4)) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+(q+4))
    let Bnu := fun j => family.normalBudget (j+(q+4))
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N p p (q+4) (q+2) Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let ha := passiveOriginalReserveAmplitude_pos Csrc rho hrho
    let globalU := passiveOriginalSmallParameter B amplitude ha b p₀
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
    ∀ (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1)),
    ∀ (HBound : ℕ → ℝ) (Rsub Lprimary : ℕ) (reserve : ℝ) (hc : 0 < reserve)
      (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
      (hBnd : ∀ j R, 0 ≤ Bnd j R) (hMg : ∀ j, 0 ≤ Mg j)
      (hDinput : ∀ j, 0 ≤ Dinput j) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k),
    ∃ cap C : ℝ, 0 < cap ∧ 0 ≤ C ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart Samples univ),
    (∀ j, parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell j H ≤ HBound j) →
    let F := fun _ : Z => scale • F0
    let hF := fun _ : Z => contMDiff_const_rescale F0 hF0 scale
    ∀ (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (target : (s : Z) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x)),
    H.val = (fun _ : P => target 0) → ∀ (primary : Λ → Set (P × M)),
    let Fp := fun _ : P => F 0
    let hFp := fun _ : P => hF 0
    let gp := passiveParameterPrimary (P := P) (0 : Z) F g
    let pj := parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart Samples univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T Fp hFp gp primary ell →
    ∀ (label : (Fin r × Bool) ↪ Fin p) (epsilon : ℝ), 0 < epsilon → epsilon < cap →
    ∀ (delta : ℝ), 0 < delta →
    (∀ i : Fin A.count, ActualOriginalPrimaryPhysicalGeometry
      (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
      (round3ParameterNativePrimary Fp gp (B.chart b))) →
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z → D → M :=
      fun l s (_ : Z) => (family.piece l).seed.coordinate s 0
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z × D → ℝ :=
      fun l s (z : Z × D) => (family.piece l).seed.cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l s z x) := fun l s (_ : Z) x => actualRescaledNormal F0 hF0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
      ((waves l).normal ((family.piece l).seed.coordinate s 0 x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count → OpenPartialHomeomorph (Z × M) (Z × D) :=
      fun l s => (family.piece l).seed.physicalChart s
    let phase : Fin r → Z × M → ℝ := fun l (z : Z × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l s z x) :=
      fun l s z x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l s (z,x) • nu l s z x)
    let probe := jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase (epsilon*ell) (q+2) a
    ProbesBackgroundNativeSharp A B Samples b (epsilon*ell) C
      (jointMixedSeedBackgroundWave (0 : Z) F hF g (q+2) (epsilon*ell) delta target probe (q+1)) := by
  obtain ⟨Tp,Pphase,hTp,hProfiles⟩ := family.exists_uniform_parameter_raw_profiles
    A hA R hR hRt B.chart Samples (fun i z hz => hQT i.2 (hSQ i z hz)) hSR
  refine ⟨Tp,Pphase,hTp,?_⟩
  intro Mgp Bchi Bnu Mphase Csrc amplitude ha globalU
  obtain ⟨_,Ku,hKu,hKu0,huSmooth,huJets⟩ := passiveOriginalSmallParameter_joint_profiles (Es := D)
    B hB Q hQ hQT amplitude ha b p₀ hp₀
  refine ⟨Ku,hKu,hKu0,?_⟩
  intro hbuffer HBound Rsub Lprimary reserve hc Bnd Mg Dinput hBnd hMg hDinput T hT
  have hMgp j : 0 ≤ Mgp j := (family.positive _).1.le
  have hBchi j : 0 ≤ Bchi j := (family.positive _).2.1.le
  have hBnu j : 0 ≤ Bnu j := (family.positive _).2.2.le
  have hMphase j : 0 ≤ Mphase j := (hTp _).2.le
  have hsmall : Csrc*amplitude^2 ≤ rho/4 := passiveOriginalReserveAmplitude_small Csrc rho hrho
  obtain ⟨hcap,C,hC,hSharp⟩ := probes_background_sharp_of_original_grouped_raw
    (S := Z) (Tr := Tr) (Λ := Λ) (Β := Β) (N := N)
    A hA B Samples hSamples hDomain rho hrho q Rsub Lprimary hq reserve hc
    Bnd Mg Dinput hBnd hMg hDinput T hT (fun _ => Tp) (fun _ k => (hTp k).1.le)
    weight Mgp Bchi Bnu Mphase Ku hMgp hBchi hBnu hMphase hKu HBound
    amplitude ha hKu0 hbuffer hsmall b p₀ hp₀
  refine ⟨_,C,hcap,hC,?_⟩
  intro scale hscale ell hell hell1 H hH F hF g target hHvalue primary Fp hFp gp pj supply
    label epsilon he hecap delta hdelta geom c chi nu a phase vf probe
  let Omega := fun (_ : ℕ) (i : Fin A.count × Fin B.count) =>
    (B.chart i.2).target ×ˢ (A.chart i.1).target
  have hOmega j i : IsOpen (Omega j i) := (B.chart i.2).open_target.prod (A.chart i.1).open_target
  have hSO j i : (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples i ⊆ Omega j i := by
    intro z hz
    exact ⟨hQT i.2 (hSQ i z hz),hRt i.1 (hSR i z hz)⟩
  let profiles := fun j i => Classical.choice (hProfiles scale hscale (j+(q+4)) j ell hell.le hell1 i)
  exact hSharp ell hell hell1 H hH (0 : Z) F hF g target hHvalue primary supply label c chi nu a phase
    Omega hOmega (fun _ _ => subset_rfl) hSO profiles
    (fun _ i => (huSmooth i.2).mono (fun _ hz => hz.1))
    (fun j i k hk z hz => huJets j ell hell.le hell1 k hk i.2 z (hSQ i z hz))
    epsilon he hecap delta hdelta geom

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_background_sharp_of_general_family
