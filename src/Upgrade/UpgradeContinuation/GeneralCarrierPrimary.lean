import NormalPolar.ActualProbeInitialSupplyCarrierAtlas
import NormalPolar.ActualProbeInitialSupplyRawScalarize
import NormalPolar.PassiveRawOrder
import NormalPolar.PassiveRawBudget
import NormalPolar.PassiveOriginalObserverNormSamples
import Main.GeneralLegalWaveObserverProfiles
import NormalPolar.PassiveWaveSeedObservation
import NormalPolar.JointSecondaryGroupedBudget

/-! The primary part of the original atlas is manufactured from the actual
q440 native background, original legal-wave family and the raw parameter
function. Constants precede every contraction and scale. Native domains,
all original samples and all original wave labels remain unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m d N r : ℕ} {M P Tr Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

theorem generalProbeInitialSupply_signed_carrier_primary_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hAll : Data.parameterSet = univ)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight) :
    ∃ Tphase : ℕ → ℝ, ∃ Pphase : ℕ → ℝ,
      (∀ k, 0 < Tphase k ∧ 0 < Pphase k) ∧
      ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (Rsub : ℕ) (reserve Bnd Mg Bfirst Mgfirst Ku Phfirst tau ell : ℝ)
      (hBnd : 0 ≤ Bnd)
      (hBfirst : actualProbeRawScalarCost 1329 885 Bnd ≤ Bfirst)
      (hMg : Mg ≤ Mgfirst) (hMgp : family.geometryBudget 1329 ≤ Mgfirst)
      (hPh : Pphase 442 ≤ Phfirst)
      (Tb Tbfirst Tpfirst : ℕ → ℝ)
      (hTb : ∀ k, Tb k ≤ Tbfirst k) (hTp : ∀ k, 1+Tphase k ≤ Tpfirst k)
      (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m)
        (Λ := Fin Data.primaryCount) (Β := Β) (fun _ : P => scale • F0))
      (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (primaryDomain : Fin Data.primaryCount → Set (P × M))
      (K : (Fin Data.primaryCount ⊕ Fin r) → Set (P × M))
      (u : P → Fin d → ℝ)
      (hu : ∀ i, ContDiffOn ℝ ∞ (fun z : X => u ((Data.parameterChart i).symm z.1))
        (Prod.fst ⁻¹' (Data.parameterChart i).target))
      (huj : ∀ k, k ≤ 442 → ∀ (i : Fin Data.parameterCount) (z : X),
        z.1 ∈ Data.parameterNormDomain i →
          ell^k*‖iteratedFDeriv ℝ k
            (fun y : X => u ((Data.parameterChart i).symm y.1)) z‖ ≤ Ku)
      (raw : ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) 1329 442 885 Rsub
          (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) reserve Bnd Mg Tb
          (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
          (round3ParameterNativePrimary (fun _ : P => scale • F0) g (Data.parameterChart i.2))
          (fun p => input ((Data.parameterChart i.2).symm p))
          (fun p => input ((Data.parameterChart i.2).symm p))
          (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)))
          (fun l => round3ParameterNativeDomain (Data.parameterChart i.2) (primaryDomain l))
          (Data.atlas.chart i.1)
          (actualRawObserverOpen (Data.atlas.chart i.1)
            (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))))
          ((parameterTensorModelEquiv (m+1) d) ⁻¹'
            incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
              Data.parameterNormDomain Data.parameterSet i) tau ell 0),
      ∃ built : ActualProbeInitialCarrierPrimaryRawAtlas (Tr := ℝ)
        Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet)
        (fun _ : P => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale) g
        (fun l s _ => (family.piece l).seed.coordinate s 0)
        (fun l s (z : P × D) => (family.piece l).seed.cutoffCoordinates s (0,z.2))
        (fun l s _ x => actualRescaledNormal F0 hF0 scale
          (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
          ((waves l).normal ((family.piece l).seed.coordinate s 0 x)))
        (fun l (z : P × M) => weight l*(waves l).phase z.2)
        (fun l s => passiveParameterChart (0 : Z) ((family.piece l).seed.physicalChart s))
        input input u univ primaryDomain K
        (fun l s => {z : P × M | (0,z.2) ∈ (family.piece l).seed.carrier s})
        1329 442 440 Rsub (Fintype.card (Fin Data.primaryCount ⊕ Fin r))
        (∑ l, (family.piece l).seed.refinement.count)
        reserve Bfirst Mgfirst (family.cutoffBudget 1329) (family.normalBudget 1329) Ku Phfirst
        tau ell 0 Tbfirst Tpfirst,
      ∀ i, built.domain i = (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target := by
  obtain ⟨Tphase,Pphase,hpos,hprofile⟩ := family.exists_observation_profiles_samples
    Data.atlas hd.atlas_smooth Data.sourceNormDomain hOmega hd.source_norm_subset
  refine ⟨Tphase,Pphase,hpos,?_⟩
  intro scale hscale Rsub reserve Bnd Mg Bfirst Mgfirst Ku Phfirst tau ell hBnd hBfirst hMg hMgp hPh
    Tb Tbfirst Tpfirst hTb hTp hell hell1 g input primaryDomain K u hu huj raw
  let Samples := incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
    Data.parameterNormDomain Data.parameterSet
  let Omega := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).target
  have hNative i : (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples i =
      Data.parameterNormDomain i.2 ×ˢ Data.sourceNormDomain i.1 :=
    passiveOriginal_native_norm_sample Data hd hAll i
  have hOpen i : actualRawObserverOpen (Data.atlas.chart i.1)
      (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))) = Omega i := by
    ext z
    simp only [actualRawObserverOpen,round3ParameterNativeDomain,Omega,mem_inter_iff,mem_preimage,mem_setOf_eq,mem_prod,mem_univ,and_true,true_and]
    exact and_comm
  refine ⟨{
    domain := Omega
    target := fun i z hz => hz.2
    background := ?_
    prescribed := ?_
    parameter_smooth := fun i => (hu i.2).mono (fun _ hz => hz.1)
    parameter_jets := ?_
    piece_overlap := ?_
    overlap := fun i z hz => (Finset.card_filter_le _ _).trans_eq (by simp) },?_⟩
  · intro i
    let scalar := actualProbeInitialSupply_raw_scalarize 1329 442 885 Rsub
      (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) reserve Bnd Mg hBnd Tb
      (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
      (round3ParameterNativePrimary (fun _ : P => scale • F0) g (Data.parameterChart i.2))
      (fun p => input ((Data.parameterChart i.2).symm p))
      (fun p => input ((Data.parameterChart i.2).symm p))
      (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)))
      (fun l => round3ParameterNativeDomain (Data.parameterChart i.2) (primaryDomain l))
      (Data.atlas.chart i.1)
      (actualRawObserverOpen (Data.atlas.chart i.1)
        (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))))
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples i) tau ell 0 (raw i)
    let lower := scalar.lowerJointOrder 441 (by omega)
    have enlarged := lower.enlargeBudgets Bfirst Mgfirst Tbfirst hBfirst hMg hTb
    rw [hOpen i] at enlarged
    exact enlarged
  · intro i
    let old := Classical.choice (hprofile scale hscale 1329 442 ell hell hell1 i.1)
    have lifted := passiveWaveSeed_observation (Data.parameterChart i.2) (Data.atlas.chart i.1)
      (fun _ : Z => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
      (fun l s _ => (family.piece l).seed.coordinate s 0)
      (fun l s => (family.piece l).seed.cutoffCoordinates s)
      (fun l s _ x => actualRescaledNormal F0 hF0 scale
        (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
        ((waves l).normal ((family.piece l).seed.coordinate s 0 x)))
      (fun l s => ((family.piece l).seed.physicalChart s)) univ
      (fun l s => (family.piece l).seed.carrier s) 1329 442 ell
      (family.geometryBudget 1329) (family.cutoffBudget 1329) (family.normalBudget 1329) hell
      ((univ : Set Z) ×ˢ (Data.atlas.chart i.1).target)
      ((univ : Set Z) ×ˢ Data.sourceNormDomain i.1)
      (fun z hz => ⟨hz.1,hd.source_norm_subset i.1 hz.2⟩)
      Tphase (fun k => (hpos k).1.le)
      (fun l (z : Z × M) => weight l*(waves l).phase z.2) (Pphase 442) old
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples i)
      (fun z hz => hd.parameter_norm_subset i.2 ((hNative i ▸ hz).1))
      (fun z hz => ⟨mem_univ _,(hNative i ▸ hz).2⟩)
    have hDom : {z : X | z.1 ∈ (Data.parameterChart i.2).target ∧
        (0,z.2) ∈ ((univ : Set Z) ×ˢ (Data.atlas.chart i.1).target)} = Omega i := by
      ext z
      simp only [Omega,mem_setOf_eq,mem_prod,mem_univ,true_and]
    rw [hDom] at lifted
    exact lifted.enlargeBudgets Mgfirst (family.cutoffBudget 1329) (family.normalBudget 1329)
      Phfirst Tpfirst hMgp le_rfl le_rfl hPh hTp
  · intro i k hk z hz
    exact huj k hk i.2 z ((hNative i ▸ hz).1)
  · intro i l z hz
    have hl : (family.piece l).seed.refinement.count ≤ ∑ l', (family.piece l').seed.refinement.count :=
      Finset.single_le_sum (f := fun l : Fin r => (family.piece l).seed.refinement.count)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    exact ((Finset.card_filter_le _ _).trans_eq (by simp)).trans hl

  · intro i
    rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.generalProbeInitialSupply_signed_carrier_primary_uniform
