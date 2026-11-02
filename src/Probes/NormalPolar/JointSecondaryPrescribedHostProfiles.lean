import NormalPolar.OriginalWaveSeedObserverBounds
import NormalPolar.OriginalWaveSeedObservationProfiles

/-! Genuine grouped primary observation profiles on any fixed finite set
of maximal-atlas hosts and compact coordinate samples. These are additional
observations of the same original waves. The original atlas and norm domains
are not replaced, and no estimate from a different host is reused. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Upgrade
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N r : ℕ} {M Host : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [Fintype Host]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

theorem jointSecondary_prescribed_finite_host_profiles
    (family : OriginalWaveSeedFamily F hF waves weight)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ h, host h ∈ maximalAtlas IM ∞ M)
    (R : Host → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (host h).target) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ h : Host,
      Nonempty (JointGroupedPrescribedObservationProfiles
        (fun _ : Z => F) (fun _ => hF)
        (fun l s _ => (family.outer l s).spatialChart.symm)
        (fun l s => (family.refinement l).cutoffCoordinates s)
        (fun l s _ x => (waves l).normal ((family.outer l s).spatialChart.symm x))
        (fun l s => (family.inner l s).chart)
        univ (fun l s => tsupport ((family.refinement l).cutoff s))
        n j ell (family.geometryBudget (max n j)) (family.cutoffBudget n) (family.normalBudget n)
        (fun z : X => (z.1,(host h).symm z.2))
        ((univ : Set Z) ×ˢ (host h).target) ((univ : Set Z) ×ˢ R h)
        T (fun l z => weight l * (waves l).phase z.2) (Pphase j)) := by
  let S (h : Host) := (host h).symm '' R h
  have hS (h : Host) : IsCompact (S h) :=
    (hR h).image_of_continuousOn ((host h).symm.continuousOn.mono (hRt h))
  have hSs (h : Host) : S h ⊆ (host h).source := by
    rintro x ⟨y,hy,rfl⟩
    exact (host h).map_target (hRt h hy)
  let Idx := Host × ((l : Fin r) × Fin (family.refinement l).count)
  let Sample (idx : Idx) := OriginalWaveSeedBuffer.observerActiveSample
    (host idx.1) (S idx.1) (family.refinement idx.2.1) idx.2.2
  let Domain (idx : Idx) := (family.inner idx.2.1 idx.2.2).observerDomain (host idx.1)
  have hSample (idx : Idx) : IsCompact (Sample idx) :=
    (family.inner idx.2.1 idx.2.2).observer_sample_compact _ _ (hS _) (hSs _)
  have hDomain (idx : Idx) : IsOpen (Domain idx) :=
    (family.inner idx.2.1 idx.2.2).observerDomain_open _
  have hSD (idx : Idx) : Sample idx ⊆ Domain idx :=
    (family.inner idx.2.1 idx.2.2).observer_sample_domain _ _ (hSs _)
  choose CT hCT bT using (fun idx : Idx => exists_compact_native_prefix
    (Sample idx) (Domain idx) (hSample idx) (hDomain idx) (hSD idx) _
    ((family.inner idx.2.1 idx.2.2).observer_transition_smooth _ (hhost _)))
  choose CP hCP bP using (fun idx : Idx => exists_compact_native_prefix
    (Sample idx) (Domain idx) (hSample idx) (hDomain idx) (hSD idx) _
    ((family.inner idx.2.1 idx.2.2).observer_phase_smooth _ (hhost _)))
  choose BT hBT using fun k => Finite.exists_le (fun idx : Idx => CT idx k)
  choose BP hBP using fun k => Finite.exists_le (fun idx : Idx => CP idx k)
  have hactive (h : Host) (l : Fin r) (s : Fin (family.refinement l).count) (z : X)
      (hz : z ∈ (univ : Set Z) ×ˢ R h)
      (ha : (z.1,(host h).symm z.2) ∈ tsupport ((family.refinement l).cutoff s)) :
      z ∈ Sample ⟨h,l,s⟩ := by
    apply (family.inner l s).observer_active_mem_sample (host h) (S h) (hSs h) z _ ha
    exact ⟨mem_univ _,(host h).symm z.2,⟨z.2,hz.2,rfl⟩,(host h).right_inv (hRt h hz.2)⟩
  refine ⟨fun k => |BT k|+1,fun k => |BP k|+1,fun k => ⟨by positivity,by positivity⟩,?_⟩
  intro n j ell hell hell1 h
  refine ⟨{
    raw := fun l s => family.raw l s n j ell hell hell1
    domains := fun l s => (family.inner l s).observerDomain (host h)
    domains_open := fun l s => (family.inner l s).observerDomain_open _
    active_domain := fun l s => (family.inner l s).observerDomain_active _
    source := fun l s => (family.inner l s).observerDomain_source _
    transition_smooth := fun l s => (family.inner l s).observer_transition_smooth _ (hhost h)
    sample := ?_
    transition_jets := ?_
    phase_smooth := fun l s => (family.inner l s).observer_phase_smooth _ (hhost h)
    phase_jets := ?_ }⟩
  · intro l s z hz
    rw [family.raw_sample l s n j ell hell hell1]
    exact (family.inner l s).chart.map_source ((family.inner l s).cutoff_support hz.2)
  · intro l s k _ _ z hz
    have hb := bT ⟨h,l,s⟩ k k le_rfl z (hactive h l s z hz.1 hz.2)
    exact (((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hb).trans ((hBT k ⟨h,l,s⟩).trans
      ((le_abs_self _).trans (by linarith)))
  · intro l s k hkj z hz
    have hb := bP ⟨h,l,s⟩ j (k+1) (by omega) z (hactive h l s z hz.1 hz.2)
    exact (((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hb).trans ((hBP j ⟨h,l,s⟩).trans
      ((le_abs_self _).trans (by linarith)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_prescribed_finite_host_profiles
