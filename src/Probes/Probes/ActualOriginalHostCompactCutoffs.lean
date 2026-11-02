import Probes.ActualOriginalHostSampleRefinement
import Probes.ActualHostRefinementCompactSupport

/-!
# Absolute support of the actual original-host cutoffs

This consumes the native-support and source-containment conclusions of
`actual_exists_original_host_sample_refinement_with_native_support` for the
very same finite family. It supplies compact absolute supports, global
smoothness, the original relative-support identity, and a global local-count
bound. Only the source is assumed Hausdorff; it need not be compact.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter Metric
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [FiniteDimensional ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M] in
theorem actual_original_host_refinement_compact_cutoffs
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (theta : Ep × M → ℝ) (W : Set (Ep × M)) (hW : IsOpen W)
    (hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
    (s : Finset X) (b : s → OpenPartialHomeomorph X X) (r : ℝ) (hr : 0 < r)
    (hThetaSupport : incrementsGlobalRelativeSupport W theta ⊆
      (actualOriginalHostJointChart (Ep := Ep) c).source)
    (hSourceW : ∀ t : s, (actualHostAdaptedChart c (b t)).source ⊆ W)
    (hNative : ∀ t : s, tsupport (actualRefinementCutoff X s r t.val) ⊆
      (b t).source ∧ (b t).source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target) :
    let q := actualOriginalHostJointChart (Ep := Ep) c
    let eta := fun t : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s r t.val)
    ∀ t : s, IsCompact (tsupport (eta t)) ∧
      ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta t) ∧
      tsupport (eta t) ⊆ W ∧
      tsupport (eta t) ⊆ (actualHostAdaptedChart c (b t)).source ∩
        incrementsGlobalRelativeSupport W theta ∧
      incrementsGlobalRelativeSupport W (eta t) = tsupport (eta t) := by
  intro q eta t
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source := by
    have hcs : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓙 ∞
        (fun z : Ep × M => c z.2) q.source :=
      (contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    exact contMDiffOn_fst.prodMk_space hcs
  have hCompact : IsCompact (tsupport (actualRefinementCutoff X s r t.val)) :=
    (isCompact_closedBall t.val (2*r)).of_isClosed_subset (isClosed_tsupport _)
      (actualRefinementCutoff_tsupport X s r hr t.val)
  have hTarget : tsupport (actualRefinementCutoff X s r t.val) ⊆ q.target :=
    (hNative t).1.trans (hNative t).2
  have hMap : MapsTo q.symm (tsupport (actualRefinementCutoff X s r t.val)) W := by
    intro y hy
    apply hSourceW t
    change q.symm y ∈ q.source ∧ q (q.symm y) ∈ (b t).source
    exact ⟨q.map_target (hTarget hy),by simpa only [q.right_inv (hTarget hy)] using (hNative t).1 hy⟩
  obtain ⟨hCompactEta,hEtaW,hGlobal,hSupport⟩ := actual_host_cutoff_compact_global_support
    q theta (actualRefinementCutoff X s r t.val) W hW hTheta hThetaSupport hq
    (actualRefinementCutoff_contDiff X s r t.val) hCompact hTarget hMap
  refine ⟨hCompactEta,hGlobal,hEtaW,?_,?_⟩
  · intro z hz
    have hh := hSupport hz
    exact ⟨⟨hh.2.1,(hNative t).1 hh.2.2⟩,hh.1⟩
  · rw [parameterRound2_global_relativeSupport_eq W hW]
    exact inter_eq_right.mpr hEtaW

omit [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M] in
theorem actual_original_host_refinement_absolute_local_count
    (s : Finset X) (eta : s → Ep × M → ℝ) (W : Set (Ep × M)) (L : ℕ)
    (hSupportW : ∀ t : s, tsupport (eta t) ⊆ W)
    (hRelative : ∀ t : s, incrementsGlobalRelativeSupport W (eta t) = tsupport (eta t))
    (hCount : ∀ z ∈ W,
      (Finset.univ.filter (fun t : s => z ∈ incrementsGlobalRelativeSupport W (eta t))).card ≤ L) :
    ∀ z, (Finset.univ.filter (fun t : s => z ∈ tsupport (eta t))).card ≤ L := by
  intro z
  by_cases hz : z ∈ W
  · simpa only [hRelative] using hCount z hz
  · have he : (Finset.univ.filter (fun t : s => z ∈ tsupport (eta t))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hz (hSupportW t (Finset.mem_filter.mp ht).2)
    simp only [he,Finset.card_empty,Nat.zero_le]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_host_refinement_compact_cutoffs
#print axioms GlobalEmbedding.Continuation.actual_original_host_refinement_absolute_local_count
