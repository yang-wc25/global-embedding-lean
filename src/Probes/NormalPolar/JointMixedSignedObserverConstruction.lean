import NormalPolar.JointSecondarySignedObserverFamily
import NormalPolar.JointMixedNativeObservation

/-! A genuine complete native observer certificate produced from the actual
signed seeds, original compact atlas support, and original parameter chart.
All overlap counts are the finite family cardinalities. No observation jets,
wave estimates, forcing estimates or defect bounds are input hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep P Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
  [Fintype Label] [DecidableEq Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
local notation "Rec" => ActualSecondarySignedRecord Label
local instance : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem jointMixedSignedObserver_from_actual_seeds
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (phase : Rec → M → ℝ) (K : Label → Set M) (O : Rec → Set M)
    (seeds : (r : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (phase r)
      (K r.val.1.1 ∩ K r.val.1.2) (O r))
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧
      ∀ (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target)
      (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
      (n j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (he1 : ell ≤ 1),
      Nonempty (JointMixedNativeObserverGeometry (fun _ : Ep => scale • F)
        (fun _ => contMDiff_const_rescale F hF scale) n j ell
        (jointSecondarySeedGeometryBudget seeds (max n (j+1)))
        (round3ParameterNativeDomain B (univ : Set (P × M)))
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n (j+1) ell hell he1)
        e (B.target ×ˢ e.target) (Q ×ˢ (e '' S))
        (fun l => round3ParameterNativeDomain B ((univ : Set P) ×ˢ K l))
        (Fintype.card Label) (Fintype.card (Σ r, Fin (seeds r).refinement.count)) T) := by
  obtain ⟨T,hT,hbound⟩ := jointSecondarySignedNativeRaw_observer_jets_uniform
    (P := P) seeds e he S hS hSe
  refine ⟨T,hT,?_⟩
  intro B Q hQ scale hs n j ell hell he1
  let g := jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n (j+1) ell hell he1
  let trans := fun r s => ((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (g r s).chart
  have hSt : e '' S ⊆ e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hSe hx)
  have hFs : ContDiffOn ℝ ∞ ((scale • F) ∘ e.symm) e.target :=
    ((contMDiff_const_rescale F hF scale).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  refine ⟨{
    host_maximal := he
    target := fun z hz => hz.2
    ambient_smooth := hFs.comp contDiffOn_snd (fun z hz => hz.2)
    primary_support := ?_
    transition_smooth := fun r s => jointSecondarySignedNativeRaw_transition_smooth
      seeds B Q hQ S e he scale hs n (j+1) ell hell he1 r s
    inverse_smooth := fun r s => jointSecondarySignedNativeRaw_transition_inverse_smooth
      seeds B Q hQ S e he scale hs n (j+1) ell hell he1 r s
    localDomain := fun r s => (B.target ×ˢ e.target) ∩ (trans r s).source
    local_open := fun r s => (B.open_target.prod e.open_target).inter (trans r s).open_source
    local_subset := fun _ _ _ hz => hz.1
    active_local := ?_
    source := fun _ _ _ hz => hz.2.2
    active_sample := fun r s z hz => jointSecondarySignedNativeRaw_active_sample
      seeds B Q hQ S e hSe scale hs n (j+1) ell hell he1 r s z hz.1 hz.2
    transition_bound := fun r s z hz k hk _ =>
      hbound B Q hQ scale hs n (j+1) ell hell he1 r s z hz.1 hz.2 k hk
    primary_count := fun _ _ => (Finset.card_filter_le _ _).trans_eq (by simp)
    secondary_count := fun _ _ _ => (Finset.card_filter_le _ _).trans_eq (by simp) }⟩
  · intro r s z hz
    rw [jointSecondarySignedNativeRaw_support] at hz
    by_cases h : s.1 = r
    · simp only [if_pos h,round3ParameterNativeDomain,mem_setOf_eq,mem_prod,mem_univ,true_and] at hz ⊢
      exact ⟨⟨hz.1,hz.2.2.1⟩,⟨hz.1,hz.2.2.2⟩⟩
    · simp only [if_neg h,mem_empty_iff_false] at hz
  · intro r s z hz
    refine ⟨⟨hQ hz.1.1,hSt hz.1.2⟩,?_⟩
    exact jointSecondarySignedNativeRaw_active_local seeds B Q hQ S e hSe
      scale hs n (j+1) ell hell he1 r s z hz.1 hz.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixedSignedObserver_from_actual_seeds
