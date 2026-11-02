import NormalPolar.PassiveOriginalSignedObserverSamples
import Smoothing.ParameterGeometryJets

/-! Actual cutoff, normal and spatial phase covector in an additional host.
All joint derivative constants come from the original smooth fields on the
fixed compact active sample. They precede every reconstruction scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

def passiveOriginalObserverPhysicalPoint
    (B : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D) (z : X) : P × M :=
  (B.symm z.1,host.symm z.2)

def passiveOriginalObserverFieldDomain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (ip : Fin Data.parameterCount)
    (host : OpenPartialHomeomorph M D) : Set X :=
  ((Data.parameterChart ip).target ×ˢ host.target) ∩
    (passiveOriginalObserverPhysicalPoint (Data.parameterChart ip) host) ⁻¹'
      (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)

theorem passiveOriginal_observer_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (ip : Fin Data.parameterCount)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverFieldDomain Data nu ip host) :
    let Omega := passiveOriginalObserverFieldDomain Data nu ip host
    let point := passiveOriginalObserverPhysicalPoint (Data.parameterChart ip) host
    let chi := Data.cutoff nu ∘ point
    let normal := Data.freeNormal nu ∘ point
    let phase := Data.phase nu ∘ point
    let gradient := fun z : X => fderiv ℝ (fun y => phase (z.1,y)) z.2
    IsOpen Omega ∧ ContDiffOn ℝ ∞ chi Omega ∧ ContDiffOn ℝ ∞ normal Omega ∧
      ContDiffOn ℝ ∞ phase Omega ∧ ContDiffOn ℝ ∞ gradient Omega ∧
      ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
        ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ n k, k ≤ n → ∀ z ∈ R,
          ell^k*‖iteratedFDeriv ℝ k chi z‖ ≤ C n ∧
          ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤ C n ∧
          ell^k*‖iteratedFDeriv ℝ k gradient z‖ ≤ C n := by
  intro Omega point chi normal phase gradient
  let H := (Data.parameterChart ip).target ×ˢ host.target
  have hp : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞ point H := by
    have h1 := (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth ip)).comp
      (contDiffOn_fst.contMDiffOn : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ Prod.fst H)
      (fun z hz => hz.1)
    have h2 := (contMDiffOn_symm_of_mem_maximalAtlas hhost).comp
      (contDiffOn_snd.contMDiffOn : ContMDiffOn 𝓘(ℝ,X) IM ∞ Prod.snd H)
      (fun z hz => hz.2)
    exact h1.prodMk h2
  have hOmega : IsOpen Omega := hp.continuousOn.isOpen_inter_preimage
    ((Data.parameterChart ip).open_target.prod host.open_target)
    ((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ))
  have hp0 := hp.mono (show Omega ⊆ H from inter_subset_left)
  have hm : MapsTo point Omega (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :=
    fun z hz => hz.2
  have hc : ContDiffOn ℝ ∞ chi Omega := ((hs.cutoff_joint nu).comp hp0 hm).contDiffOn
  have hn : ContDiffOn ℝ ∞ normal Omega := ((hs.normal_joint nu).comp hp0 hm).contDiffOn
  have hphase : ContDiffOn ℝ ∞ phase Omega := ((hs.phase_joint nu).comp hp0 hm).contDiffOn
  have hg : ContDiffOn ℝ ∞ gradient Omega :=
    (incrementsJointSpatialJets_bridge phase Omega hOmega hphase).2.1
  obtain ⟨Cc,hCc,hcb⟩ := exists_compact_native_prefix R Omega hR hOmega hRO chi hc
  obtain ⟨Cn,hCn,hnb⟩ := exists_compact_native_prefix R Omega hR hOmega hRO normal hn
  obtain ⟨Cg,hCg,hgb⟩ := exists_compact_native_prefix R Omega hR hOmega hRO gradient hg
  refine ⟨hOmega,hc,hn,hphase,hg,fun n => Cc n+Cn n+Cg n,
    fun n => by linarith [hCc n,hCn n,hCg n],?_⟩
  intro ell hell hell1 n k hk z hz
  have hh (f : X → ℝ) (K : ℝ) (hb : ‖iteratedFDeriv ℝ k f z‖ ≤ K) :
      ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ K :=
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq (one_mul _)).trans hb
  refine ⟨(hh chi (Cc n) (hcb n k hk z hz)).trans (by linarith [hCn n,hCg n]),?_,?_⟩
  · have h : ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤ Cn n := ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1)
        (norm_nonneg (iteratedFDeriv ℝ k normal z))).trans_eq (one_mul _)).trans (hnb n k hk z hz)
    linarith [hCc n,hCg n]
  · have h : ell^k*‖iteratedFDeriv ℝ k gradient z‖ ≤ Cg n := ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1)
        (norm_nonneg (iteratedFDeriv ℝ k gradient z))).trans_eq (one_mul _)).trans (hgb n k hk z hz)
    linarith [hCc n,hCn n]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_observer_fields
