import Probes.Round3ParameterNativeEtaSmooth
import Probes.Round3PreparedCompactProfiles

/-! True EFFECTIVE-CARRIER cross-parameter-chart profiles on the ORIGINAL compact
observation samples. Forward, inverse and subordinate-cutoff total jets are
produced together, for every order and every later scale, from one literal
physical chart and eta. No derivative budget is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_parameter_carrier_observer_profiles
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (hPreserves : Round3ParameterChartPreserves a)
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a a.source)
    (hai : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target)
    (eta : P × M → ℝ) (hEta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ eta)
    (carrier : Set (P × M)) (hClosed : IsClosed carrier)
    (hCarrierSource : carrier ⊆ a.source)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (S : Set X) (hS : IsCompact S) (hST : S ⊆ B.target ×ˢ e.target) :
    let aN := round3ParameterChartPullback B a
    let t := ((OpenPartialHomeomorph.refl Ep).prod e).symm.trans aN
    let etaN := fun z : X => eta (B.symm (aN.symm z).1,(aN.symm z).2)
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ k z,
        z ∈ S ∩ (fun z : X => (B.symm z.1,e.symm z.2)) ⁻¹' carrier →
        z ∈ t.source ∧ t z ∈ t.target ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧
        ell^k*‖iteratedFDeriv ℝ k etaN (t z)‖ ≤ Meta k := by
  intro aN t etaN
  let q := B.prod e
  let K := S ∩ q.symm ⁻¹' carrier
  have hK : IsCompact K := hS.of_isClosed_subset
    ((q.symm.continuousOn.mono hST).preimage_isClosed_of_isClosed hS.isClosed hClosed)
    inter_subset_left
  have hKS : K ⊆ t.source := by
    intro z hz
    have ht := hST hz.1
    refine ⟨⟨mem_univ _,ht.2⟩,?_⟩
    exact (round3ParameterChartPullback_source_iff B a hPreserves (z.1,e.symm z.2) ht.1).mpr
      (hCarrierSource hz.2)
  have hNative := round3ParameterChartPullback_smooth B hB a ha hai
  have htSmooth := round3Parameter_native_observer_transition_smooth aN hNative.1 hNative.2 e he
  let Ka := t '' K
  have hKa : IsCompact Ka := hK.image_of_continuousOn (t.continuousOn.mono hKS)
  have hKaT : Ka ⊆ t.target := by
    rintro _ ⟨z,hz,rfl⟩
    exact t.map_source (hKS hz)
  have hKaA : Ka ⊆ aN.target := fun z hz => (hKaT hz).1
  have hEtaSmooth := round3Parameter_native_eta_target_smooth B hB a hPreserves ha hai eta hEta
  obtain ⟨Tf,hTf,hForw⟩ := round3_prepared_compact_profiles t t.source K t.open_source hK hKS htSmooth.1
  obtain ⟨Ti,hTi,hInv⟩ := round3_prepared_compact_profiles t.symm t.target Ka t.open_target hKa hKaT htSmooth.2
  obtain ⟨Te,hTe,hMeta⟩ := round3_prepared_compact_profiles etaN aN.target Ka aN.open_target hKa hKaA hEtaSmooth
  refine ⟨Tf,Ti,Te,hTf,hTi,hTe,?_⟩
  intro ell hell hell1 k z hz
  have hzk : z ∈ K := hz
  exact ⟨hKS hzk,t.map_source (hKS hzk),(hForw ell hell hell1 k z hzk).2,
    (hInv ell hell hell1 k (t z) ⟨z,hzk,rfl⟩).2,(hMeta ell hell hell1 k (t z) ⟨z,hzk,rfl⟩).1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_carrier_observer_profiles
