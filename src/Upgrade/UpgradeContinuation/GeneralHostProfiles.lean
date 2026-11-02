import Main.GeneralLegalWaveObserverProfiles

/-!
# Actual finite-host observer profiles for the general raw family

The existing generic signed-buffer observer supplies the actual transition
domains, smoothness and compact active samples. All transition and phase
prefix costs are chosen on these real compact sets before contraction,
orders and scale. The given original coordinate sampling set is retained.
-/

noncomputable section
open Set Function Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {m N r : ℕ} {M Host : Type*} [Fintype Host]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]

local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace GeneralLegalWaveRawFamily

theorem exists_finite_host_profiles (d : GeneralLegalWaveRawFamily F hF waves weight)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ h, host h ∈ maximalAtlas IM ∞ M)
    (R : Host → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (host h).target) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
        (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ h : Host,
      Nonempty (JointGroupedPrescribedObservationProfiles (I := IM)
        (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
        (fun l s => (d.piece l).seed.coordinate s)
        (fun l s => (d.piece l).seed.cutoffCoordinates s)
        (fun l s => (d.piece l).seed.scaledNormal scale hs s)
        (fun l s => (d.piece l).seed.physicalChart s)
        univ (fun l s => (d.piece l).seed.carrier s)
        n j ell (d.geometryBudget (max n j)) (d.cutoffBudget n) (d.normalBudget n)
        (fun z : X => (z.1,(host h).symm z.2))
        ((univ : Set Z) ×ˢ (host h).target) ((univ : Set Z) ×ˢ R h)
        T (fun l (z : Z × M) => weight l * (waves l).phase z.2) (Pphase j)) := by
  let Source (h : Host) : Set M := (host h).symm '' R h
  have hSource (h : Host) : IsCompact (Source h) :=
    (hR h).image_of_continuousOn ((host h).symm.continuousOn.mono (hRt h))
  have hSourceChart (h : Host) : Source h ⊆ (host h).source := by
    rintro x ⟨y,hy,rfl⟩
    exact (host h).map_target (hRt h hy)
  have hImage (h : Host) : (host h) '' Source h = R h := by
    ext y
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      simpa only [(host h).right_inv (hRt h hz)] using hz
    · intro hy
      exact ⟨(host h).symm y,⟨y,hy,rfl⟩,(host h).right_inv (hRt h hy)⟩
  let Idx := (h : Host) × (l : Fin r) × Fin (d.piece l).seed.refinement.count
  let S (idx : Idx) : Set X := JointSecondarySignedBuffer.observerActiveSample
    (host idx.1) (Source idx.1) (d.piece idx.2.1).seed.refinement idx.2.2
  let O (idx : Idx) : Set X :=
    ((d.piece idx.2.1).seed.inner idx.2.2).observerDomain (host idx.1)
  have hS (idx : Idx) : IsCompact (S idx) :=
    ((d.piece idx.2.1).seed.inner idx.2.2).observer_sample_compact
      _ _ (hSource _) (hSourceChart _)
  have hO (idx : Idx) : IsOpen (O idx) :=
    ((d.piece idx.2.1).seed.inner idx.2.2).observerDomain_open _
  have hSO (idx : Idx) : S idx ⊆ O idx :=
    ((d.piece idx.2.1).seed.inner idx.2.2).observer_sample_domain _ _ (hSourceChart _)
  have ht (idx : Idx) := exists_compact_native_prefix (S idx) (O idx)
    (hS idx) (hO idx) (hSO idx) _
    (((d.piece idx.2.1).seed.inner idx.2.2).observer_transition_smooth _ (hhost _))
  have hp (idx : Idx) := exists_compact_native_prefix (S idx) (O idx)
    (hS idx) (hO idx) (hSO idx) _
    (d.observer_phase_smooth idx.2.1 idx.2.2 (host idx.1) (hhost _))
  choose CT hCT bT using ht
  choose CP hCP bP using hp
  let T (k : ℕ) : ℝ := 1 + ∑ idx : Idx, CT idx k
  let Pphase (k : ℕ) : ℝ := 1 + ∑ idx : Idx, CP idx k
  have hT (k : ℕ) : 0 < T k := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun idx _ => (hCT idx k).le))
  have hP (k : ℕ) : 0 < Pphase k := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun idx _ => (hCP idx k).le))
  have hCTle (idx : Idx) (k : ℕ) : CT idx k ≤ T k :=
    (Finset.single_le_sum (fun idx _ => (hCT idx k).le) (Finset.mem_univ idx)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hCPle (idx : Idx) (k : ℕ) : CP idx k ≤ Pphase k :=
    (Finset.single_le_sum (fun idx _ => (hCP idx k).le) (Finset.mem_univ idx)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmem (h : Host) (l : Fin r) (s : Fin (d.piece l).seed.refinement.count)
      (z : X) (hz : z ∈ (univ : Set Z) ×ˢ R h)
      (ha : (z.1,(host h).symm z.2) ∈ (d.piece l).seed.carrier s) :
      z ∈ S ⟨h,l,s⟩ := by
    apply ((d.piece l).seed.inner s).observer_active_mem_sample
      (host h) (Source h) (hSourceChart h) z
    · exact ⟨mem_univ _,by rw [hImage]; exact hz.2⟩
    · exact ha.2.1
  refine ⟨T,Pphase,fun k => ⟨hT k,hP k⟩,?_⟩
  intro scale hs n j ell he he1 h
  refine ⟨{
    raw := fun l s => d.raw scale hs l s n j ell he he1
    domains := fun l s => ((d.piece l).seed.inner s).observerDomain (host h)
    domains_open := fun l s => ((d.piece l).seed.inner s).observerDomain_open _
    active_domain := ?_
    source := fun l s => ((d.piece l).seed.inner s).observerDomain_source _
    transition_smooth := fun l s =>
      ((d.piece l).seed.inner s).observer_transition_smooth _ (hhost _)
    sample := ?_
    transition_jets := ?_
    phase_smooth := fun l s => d.observer_phase_smooth l s _ (hhost _)
    phase_jets := ?_ }⟩
  · intro l s z hz
    exact ((d.piece l).seed.inner s).observerDomain_active _ ⟨hz.1,hz.2.2.1⟩
  · intro l s z hz
    rw [d.raw_sample]
    exact ((d.piece l).seed.physicalChart s).map_source
      ⟨mem_univ _,((d.piece l).seed.inner s).support_source hz.2.2.1⟩
  · intro l s k _ _ z hz
    have hb := bT ⟨h,l,s⟩ k k le_rfl z (hmem h l s z hz.1 hz.2)
    exact (((mul_le_mul_of_nonneg_right (pow_le_one₀ he he1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hb).trans (hCTle ⟨h,l,s⟩ k)
  · intro l s k hkj z hz
    have hb := bP ⟨h,l,s⟩ j (k+1) (by omega) z (hmem h l s z hz.1 hz.2)
    exact (((mul_le_mul_of_nonneg_right (pow_le_one₀ he he1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hb).trans (hCPle ⟨h,l,s⟩ j)

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.exists_finite_host_profiles
