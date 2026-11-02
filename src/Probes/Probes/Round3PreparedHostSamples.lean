import Probes.Round3PreparedCompactProfiles
import Probes.ActualIncrementHostGeometryInputs
import Probes.ActualFinalCanonicalHostDomains

/-! Actual compact observation sets determine one all-order prepared packet.
The adapted sample is the image of the true physical samples on the effective
interaction carrier. Host and observer sample inclusions, cutoff jets and true
inverse-transition jets are proved together for that one sample. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round3_prepared_host_samples_and_profiles
    {Index : Type*} [Fintype Index]
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b psi e)
    (rho : Ep × M → ℝ)
    (hrho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (carrier K : Set (Ep × M)) (hCarrier : IsCompact carrier) (hK : IsCompact K)
    (hSource : carrier ⊆ (actualHostAdaptedChart c b).source)
    (observer : Index → OpenPartialHomeomorph M D)
    (hObserver : ∀ i, observer i ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (Samples : Index → Set X) (hSamples : ∀ i, IsCompact (Samples i))
    (hTarget : ∀ i, Samples i ⊆ (actualOriginalHostJointChart (Ep := Ep) (observer i)).target)
    (hPhysical : ∀ i, MapsTo (fun z : X => (z.1,(observer i).symm z.2)) (Samples i) K)
    (HostSamples : Set X)
    (hNative : MapsTo (actualOriginalHostJointChart (Ep := Ep) c) (K ∩ carrier) HostSamples) :
    let q := actualOriginalHostJointChart (Ep := Ep) c
    let a := actualHostAdaptedChart c b
    let S := a '' (K ∩ carrier)
    ∃ Tinv Kcut Tobs : ℕ → ℝ,
      (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Kcut k) ∧ (∀ k, 0 ≤ Tobs k) ∧
      IsCompact S ∧ S ⊆ b.target ∧
      MapsTo b.symm S HostSamples ∧
      (q.symm.trans a).symm '' S ⊆ HostSamples ∧
      (∀ i z, z ∈ Samples i ∩ (fun z : X => (z.1,(observer i).symm z.2)) ⁻¹' carrier →
        a (z.1,(observer i).symm z.2) ∈ S) ∧
      ContDiffOn ℝ ∞ (rho ∘ q.symm) (q.symm.trans a).source ∧
      ContDiffOn ℝ ∞ (q.symm.trans a).symm (q.symm.trans a).target ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 →
        (∀ k z, z ∈ S → ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ Tinv k) ∧
        (∀ k z, z ∈ S → ell^(k-1)*‖iteratedFDeriv ℝ k (q.symm.trans a).symm z‖ ≤ Tinv k) ∧
        (∀ n k, k ≤ n → ∀ z ∈ S,
          ell^k*‖iteratedFDeriv ℝ k (rho ∘ q.symm) ((q.symm.trans a).symm z)‖ ≤ Kcut n) ∧
        (∀ i z, z ∈ Samples i ∩ (fun z : X => (z.1,(observer i).symm z.2)) ⁻¹' carrier →
          ∀ k, ell^(k-1)*‖iteratedFDeriv ℝ k
            (a ∘ (fun z : X => (z.1,(observer i).symm z.2))) z‖ ≤ Tobs k) := by
  intro q a S
  obtain ⟨hNativeTarget,hb,hbi,_⟩ := actual_host_slice_geometry_inputs c hc b psi e hdata
  have hKS : K ∩ carrier ⊆ a.source := inter_subset_right.trans hSource
  have hCompactKS : IsCompact (K ∩ carrier) := hK.inter_right hCarrier.isClosed
  have hS : IsCompact S := hCompactKS.image_of_continuousOn (a.continuousOn.mono hKS)
  have hSb : S ⊆ b.target := by
    rintro _ ⟨y,hy,rfl⟩
    rw [← hdata.1]
    exact a.map_source (hKS hy)
  have hNativeIdentity (y : Ep × M) (hy : y ∈ K ∩ carrier) : b.symm (a y) = q y := by
    change b.symm (b (q y)) = q y
    exact b.left_inv (hKS hy).2
  have hSampleNative : MapsTo b.symm S HostSamples := by
    rintro _ ⟨y,hy,rfl⟩
    rw [hNativeIdentity y hy]
    exact hNative hy
  have hT := round3_prepared_host_transition_domains c b hNativeTarget
  have hSmooth := round3_prepared_host_transition_smooth c hc b psi e hdata hNativeTarget rho hrho
  have hTransSample : (q.symm.trans a).symm '' S ⊆ HostSamples := by
    rintro _ ⟨y,hy,rfl⟩
    rw [hT.2.2.2 (hSb hy)]
    exact hSampleNative hy
  have hBackCompact : IsCompact (b.symm '' S) :=
    hS.image_of_continuousOn (b.symm.continuousOn.mono hSb)
  have hBackDomain : b.symm '' S ⊆ (q.symm.trans a).source := by
    rw [hT.1]
    rintro _ ⟨y,hy,rfl⟩
    exact b.map_target (hSb hy)
  obtain ⟨Tinv,hTinv,hInv⟩ := round3_prepared_compact_profiles
    b.symm b.target S b.open_target hS hSb hbi
  obtain ⟨Cut,hCut,hCutBound⟩ := round3_prepared_compact_profiles
    (rho ∘ q.symm) (q.symm.trans a).source (b.symm '' S)
    (q.symm.trans a).open_source hBackCompact hBackDomain hSmooth.1
  obtain ⟨Tobs,hTobs,hObs⟩ := round3_prepared_observer_profiles
    a hdata.2.1 carrier hCarrier hSource observer hObserver Samples hSamples hTarget
  let Kcut := fun n => ∑ k ∈ Finset.range (n+1), Cut k
  have hKcut (n : ℕ) : 0 ≤ Kcut n := Finset.sum_nonneg (fun k _ => hCut k)
  refine ⟨Tinv,Kcut,Tobs,hTinv,hKcut,hTobs,hS,hSb,hSampleNative,hTransSample,?_,hSmooth.1,hSmooth.2,?_⟩
  · intro i z hz
    exact ⟨_,⟨hPhysical i hz.1,hz.2⟩,rfl⟩
  · intro ell hell hell1
    refine ⟨fun k z hz => (hInv ell hell hell1 k z hz).2,?_,?_,hObs ell hell hell1⟩
    · intro k z hz
      rw [(round3_prepared_host_transition_jets c b hNativeTarget).2 k z (hSb hz)]
      exact (hInv ell hell hell1 k z hz).2
    · intro n k hk z hz
      rw [hT.2.2.2 (hSb hz)]
      apply (hCutBound ell hell hell1 k _ ⟨z,hz,rfl⟩).1.trans
      exact Finset.single_le_sum (fun i _ => hCut i) (by simpa using hk)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_host_samples_and_profiles
