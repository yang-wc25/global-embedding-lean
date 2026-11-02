import GlobalEmbedding.Paper.FreeCompactPivotPerturbation

/-! A genuine compact injective frame produces a positive lower bound on a
true open neighborhood of the same compact carrier. The neighborhood is
constructed from the actual frame's continuity. The bound is an output and
depends on the actual fixed compact packet, not on arbitrary later jets. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Filter
open scoped Topology
namespace GlobalEmbedding.Continuation

theorem actual_compact_frame_open_reserve
    {Q E F : Type*} [TopologicalSpace Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : Q → E →L[ℝ] F) (O K : Set Q) (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hA : ContinuousOn A O) (hinj : ∀ z ∈ K, Function.Injective (A z)) :
    ∃ (c : ℝ) (V : Set Q), 0 < c ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
      ∀ z ∈ V, ∀ v : E, c*‖v‖^2 ≤ ‖A z v‖^2 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨lam,hlam,hbase⟩ := free_compact_frame_lower_bound
    (fun p : K => A p.val) ((hA.mono hKO).domRestrict) (fun p => hinj p.val p.property)
  let V : Set Q := ⋃ p : K, O ∩ {z | ‖A p.val-A z‖ < Real.sqrt lam/2}
  have hV : IsOpen V := isOpen_iUnion (fun p : K =>
    (continuousOn_const.sub hA).norm.isOpen_inter_preimage hO isOpen_Iio)
  have hKV : K ⊆ V := by
    intro z hz
    refine mem_iUnion.mpr ⟨(⟨z,hz⟩ : K),?_⟩
    change z ∈ O ∧ ‖A z-A z‖ < Real.sqrt lam/2
    refine ⟨hKO hz,?_⟩
    simpa only [sub_self,norm_zero] using
      (div_pos (Real.sqrt_pos.mpr hlam) (by norm_num : (0:ℝ) < 2))
  have hVO : V ⊆ O := by
    intro z hz
    obtain ⟨p,hp⟩ := mem_iUnion.mp hz
    exact hp.1
  refine ⟨lam/4,V,by positivity,hV,hKV,hVO,?_⟩
  intro z hz v
  obtain ⟨p,hp⟩ := mem_iUnion.mp hz
  have h := pointwise_projected_jet_estimate (A p.val) (A z)
    (ContinuousLinearMap.id ℝ F) (ContinuousLinearMap.id ℝ F)
    lam 1 hlam (hbase p) hp.2.le ContinuousLinearMap.norm_id_le
  exact h.1 v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_compact_frame_open_reserve
