import Probes.Round3PreparedHostTransition
import Probes.ActualOriginalHostCompactCutoffs

/-! All-order profiles are outputs of the fixed, actual prepared maps.
The compact set and the map are chosen once, before the order and the later
Nash scale. No derivative budget is assumed in this compact preparation. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem round3_prepared_compact_profiles
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (O K : Set E) (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ k x, x ∈ K →
        ell^k*‖iteratedFDeriv ℝ k f x‖ ≤ C k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k f x‖ ≤ C k := by
  have hbound (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
    have hc := hf.continuousOn_iteratedFDerivWithin (m := k) (by simp) hO.uniqueDiffOn
    have hc' : ContinuousOn (iteratedFDeriv ℝ k f) K :=
      (hc.mono hKO).congr (fun x hx => (iteratedFDerivWithin_of_isOpen k hO (hKO hx)).symm)
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc'
    exact ⟨max 0 C,le_max_left _ _,fun x hx => (hC x hx).trans (le_max_right _ _)⟩
  choose C hC hbound using hbound
  refine ⟨C,hC,?_⟩
  intro ell hell hell1 k x hx
  have hpow (l : ℕ) : ell^l*‖iteratedFDeriv ℝ k f x‖ ≤ C k :=
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans (hbound k x hx)
  exact ⟨hpow k,hpow (k-1)⟩

theorem round3_prepared_finite_compact_profiles
    {I E F : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : I → E → F) (O K : I → Set E) (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, IsCompact (K i)) (hKO : ∀ i, K i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ i k x, x ∈ K i →
        ell^k*‖iteratedFDeriv ℝ k (f i) x‖ ≤ C k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k (f i) x‖ ≤ C k := by
  choose C hC hb using fun i => round3_prepared_compact_profiles
    (f i) (O i) (K i) (hO i) (hK i) (hKO i) (hf i)
  refine ⟨fun k => ∑ i, C i k,fun k => Finset.sum_nonneg (fun i _ => hC i k),?_⟩
  intro ell hell hell1 i k x hx
  have hsum : C i k ≤ ∑ a, C a k := Finset.single_le_sum (fun a _ => hC a k) (Finset.mem_univ i)
  exact ⟨((hb i ell hell hell1 k x hx).1).trans hsum,
    ((hb i ell hell hell1 k x hx).2).trans hsum⟩

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem round3_prepared_observer_profiles
    {Index : Type*} [Fintype Index]
    (a : OpenPartialHomeomorph (Ep × M) X)
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ a a.source)
    (carrier : Set (Ep × M)) (hCarrier : IsCompact carrier) (hSource : carrier ⊆ a.source)
    (observer : Index → OpenPartialHomeomorph M D)
    (hObserver : ∀ i, observer i ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (Samples : Index → Set X) (hSamples : ∀ i, IsCompact (Samples i))
    (hTarget : ∀ i, Samples i ⊆ (actualOriginalHostJointChart (Ep := Ep) (observer i)).target) :
    ∃ Tobs : ℕ → ℝ, (∀ k, 0 ≤ Tobs k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ i z,
        z ∈ Samples i ∩ (fun z : X => (z.1,(observer i).symm z.2)) ⁻¹' carrier →
        ∀ k, ell^(k-1)*‖iteratedFDeriv ℝ k
          (a ∘ (fun z : X => (z.1,(observer i).symm z.2))) z‖ ≤ Tobs k := by
  let q := fun i => actualOriginalHostJointChart (Ep := Ep) (observer i)
  have hqi (i : Index) : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (q i).symm (q i).target := by
    have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => (observer i).symm z.2) (q i).target :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hObserver i)).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  let O := fun i => (q i).target ∩ (q i).symm ⁻¹' a.source
  let K := fun i => Samples i ∩ (q i).symm ⁻¹' carrier
  have hO (i : Index) : IsOpen (O i) :=
    (hqi i).continuousOn.isOpen_inter_preimage (q i).open_target a.open_source
  have hK (i : Index) : IsCompact (K i) :=
    (hSamples i).of_isClosed_subset
      (((hqi i).continuousOn.mono (hTarget i)).preimage_isClosed_of_isClosed
        (hSamples i).isClosed hCarrier.isClosed) inter_subset_left
  have hKO (i : Index) : K i ⊆ O i := fun _ hz => ⟨hTarget i hz.1,hSource hz.2⟩
  have hf (i : Index) : ContDiffOn ℝ ∞ (a ∘ (q i).symm) (O i) :=
    (ha.comp ((hqi i).mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  obtain ⟨C,hC,hb⟩ := round3_prepared_finite_compact_profiles
    (fun i => a ∘ (q i).symm) O K hO hK hKO hf
  exact ⟨C,hC,fun ell hell hell1 i z hz k => (hb ell hell hell1 i k z hz).2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_compact_profiles
#print axioms GlobalEmbedding.Continuation.round3_prepared_finite_compact_profiles
#print axioms GlobalEmbedding.Continuation.round3_prepared_observer_profiles
