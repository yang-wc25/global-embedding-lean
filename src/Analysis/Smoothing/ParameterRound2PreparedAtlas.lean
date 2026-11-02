import Smoothing.ParameterRound2CompactPreparation
import Smoothing.ParameterRound2CompactAtlas

/-!
# Constructed compact buffered atlases with genuine raw preparations

The manifold is compact and Hausdorff. Start with an actual finite smooth
bump covering. Restrict each real chart to an open thickening of its bump's
closed coordinate ball; the closed thickening stays inside the original
smooth parent chart. A finite minimum gives one positive sampling buffer.
The smaller sampling closures have compact norm domains inside the restricted
chart targets. The actual own-cutoff and active transition profiles are then
PROVED on the compact chart extensions. They precede every field and scale.
No high-order numerical entrance hypothesis is used.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Metric Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ, E) ∞ X] [CompactSpace X] [T2Space X]

/-- Every compact smooth Hausdorff manifold admits a genuine finite buffered
atlas with actual raw cutoffs and actual finite-order geometric jet profiles.
The same atlas has compact norm domains controlling its full sampling buffers.
The construction includes the empty manifold and zero-dimensional models. -/
theorem parameterRound2_exists_compact_prepared_bufferedAtlas :
    ∃ A : BufferedAtlas X E, IsSmoothBufferedAtlas A ∧
      ∃ B₀ T : ℕ → ℝ, (∀ k, 0 ≤ B₀ k) ∧ (∀ k, 0 ≤ T k) ∧
        Nonempty (TensorRawCutoffPreparation A B₀ T A.supportDegree) ∧
        ∃ Omega : Fin A.count → Set E,
          ∀ i, IsCompact (Omega i) ∧ Omega i ⊆ (A.chart i).target ∧
            closure (bufferedSamplingCoordinates A i) ⊆ Omega i := by
  classical
  obtain ⟨ι, fs, _hsub⟩ := SmoothBumpCovering.exists_isSubordinate (I := 𝓘(ℝ, E))
    (s := (univ : Set X)) (U := fun _ => (univ : Set X)) isClosed_univ
    (fun _ _ => Filter.univ_mem)
  letI : Fintype ι := fs.fintype
  let j : Fin (Fintype.card ι) → ι := (Fintype.equivFin ι).symm
  let c (i : Fin (Fintype.card ι)) : X := fs.c (j i)
  let parent (i : Fin (Fintype.card ι)) : OpenPartialHomeomorph X E := chartAt E (c i)
  let raw (i : Fin (Fintype.card ι)) : X → ℝ := fs (j i)
  let K₀ (i : Fin (Fintype.card ι)) : Set E :=
    closedBall (parent i (c i)) (fs (j i)).rOut
  have hK₀ (i : Fin (Fintype.card ι)) : IsCompact (K₀ i) := isCompact_closedBall _ _
  have hK₀target (i : Fin (Fintype.card ι)) : K₀ i ⊆ (parent i).target := by
    simpa [K₀, parent, c, extChartAt_target, extChartAt_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm] using (fs (j i)).closedBall_subset
  have hrawImage (i : Fin (Fintype.card ι)) :
      tsupport (raw i) ⊆ (parent i).symm '' K₀ i := by
    simpa [raw, K₀, parent, c, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm] using
      (fs (j i)).tsupport_subset_symm_image_closedBall
  have hthick (i : Fin (Fintype.card ι)) : ∃ delta : ℝ, 0 < delta ∧
      cthickening delta (K₀ i) ⊆ (parent i).target :=
    (hK₀ i).exists_cthickening_subset_open (parent i).open_target (hK₀target i)
  choose delta hdelta hdeltaTarget using hthick
  let innerC (i : Fin (Fintype.card ι)) := thickening (delta i / 4) (K₀ i)
  let outerC (i : Fin (Fintype.card ι)) := thickening (delta i) (K₀ i)
  let outerS (i : Fin (Fintype.card ι)) :=
    (parent i).source ∩ (parent i) ⁻¹' outerC i
  let inner (i : Fin (Fintype.card ι)) :=
    (parent i).source ∩ (parent i) ⁻¹' innerC i
  have houterOpen (i : Fin (Fintype.card ι)) : IsOpen (outerS i) :=
    (parent i).isOpen_inter_preimage isOpen_thickening
  have hinnerOpen (i : Fin (Fintype.card ι)) : IsOpen (inner i) :=
    (parent i).isOpen_inter_preimage isOpen_thickening
  have houterTarget (i : Fin (Fintype.card ι)) : outerC i ⊆ (parent i).target :=
    (thickening_subset_cthickening _ _).trans (hdeltaTarget i)
  have hinnerOuter (i : Fin (Fintype.card ι)) : innerC i ⊆ outerC i :=
    thickening_mono (by linarith [hdelta i]) _
  let chart (i : Fin (Fintype.card ι)) := (parent i).restr (outerS i)
  have hchartSource (i : Fin (Fintype.card ι)) : inner i ⊆ (chart i).source := by
    intro x hx
    change x ∈ (parent i).source ∩ interior (outerS i)
    rw [(houterOpen i).interior_eq]
    exact ⟨hx.1, hx.1, hinnerOuter i hx.2⟩
  have hchartTarget (i : Fin (Fintype.card ι)) : (chart i).target = outerC i := by
    ext y
    change (y ∈ (parent i).target ∧ (parent i).symm y ∈ interior (outerS i)) ↔ y ∈ outerC i
    rw [(houterOpen i).interior_eq]
    constructor
    · rintro ⟨hy, hys, hyo⟩
      simpa only [Set.mem_preimage, (parent i).right_inv hy] using hyo
    · intro hy
      have ht := houterTarget i hy
      exact ⟨ht, (parent i).map_target ht, by simpa only [Set.mem_preimage, (parent i).right_inv ht] using hy⟩
  have hrawInner (i : Fin (Fintype.card ι)) : tsupport (raw i) ⊆ inner i := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hrawImage i hx
    have hyt := hK₀target i hy
    refine ⟨(parent i).map_target hyt, ?_⟩
    change parent i ((parent i).symm y) ∈ innerC i
    rw [(parent i).right_inv hyt]
    exact self_subset_thickening (div_pos (hdelta i) (by norm_num)) _ hy
  have hplateau : ∀ x, ∃ i, raw i x = 1 := by
    intro x
    refine ⟨(Fintype.equivFin ι) (fs.ind x (Set.mem_univ x)), ?_⟩
    have hj : j ((Fintype.equivFin ι) (fs.ind x (Set.mem_univ x))) = fs.ind x (Set.mem_univ x) :=
      Equiv.symm_apply_apply (Fintype.equivFin ι) _
    change (fs (j ((Fintype.equivFin ι) (fs.ind x (Set.mem_univ x))))) x = 1
    rw [hj]
    exact fs.apply_ind x (Set.mem_univ x)
  obtain ⟨eps, heps, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Fin (Fintype.card ι) => (0 : ℝ)) (y := fun i => delta i / 4)
    (fun i => div_pos (hdelta i) (by norm_num))
  let Omega (i : Fin (Fintype.card ι)) := cthickening (delta i / 2) (K₀ i)
  have hOmegaTarget (i : Fin (Fintype.card ι)) : Omega i ⊆ (chart i).target := by
    rw [hchartTarget i]
    exact cthickening_subset_thickening' (hdelta i) (by linarith [hdelta i]) _
  have hsample (i : Fin (Fintype.card ι)) {z : E} (hz : z ∈ innerC i) :
      ball z eps ⊆ Omega i := by
    have he : eps + delta i / 4 ≤ delta i / 2 := by
      have h := hsmall i
      linarith
    exact (ball_subset_thickening hz eps).trans
      ((thickening_thickening_subset eps (delta i / 4) (K₀ i)).trans
        (thickening_subset_cthickening_of_le he _))
  let A : BufferedAtlas X E := {
    count := Fintype.card ι
    chart := chart
    inner := inner
    inner_open := hinnerOpen
    inner_subset := hchartSource
    cover := by
      intro x
      obtain ⟨i, hi⟩ := hplateau x
      exact ⟨i, hrawInner i (subset_tsupport (raw i) (by change raw i x ≠ 0; rw [hi]; exact one_ne_zero))⟩
    buffer := eps
    buffer_pos := heps
    buffered := by
      intro i x hx
      exact (hsample i hx.2).trans (hOmegaTarget i)
    support := inner }
  have hA : IsSmoothBufferedAtlas A := by
    refine ⟨?_, hchartSource⟩
    intro i
    exact restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, E))
      (IsManifold.chart_mem_maximalAtlas (c i)) (houterOpen i)
  obtain ⟨B₀, T, hB₀, hT, hprep⟩ :=
    parameterRound2_exists_rawPreparation_of_compact_chart_extensions A parent
      (fun i => IsManifold.chart_mem_maximalAtlas (c i))
      (fun _ => rfl) (fun _ => rfl) (fun _ _ hx => hx.1)
      (fun i => cthickening (delta i) (K₀ i)) (fun i => (hK₀ i).cthickening)
      (fun i => by rw [hchartTarget i]; exact thickening_subset_cthickening _ _)
      hdeltaTarget raw (fun i => (fs (j i)).contMDiff) hplateau hrawInner hrawInner
  refine ⟨A, hA, B₀, T, hB₀, hT, hprep, Omega, ?_⟩
  intro i
  refine ⟨(hK₀ i).cthickening, hOmegaTarget i, ?_⟩
  apply closure_minimal _ isClosed_cthickening
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzt : z ∈ (chart i).target := hzInner.1
  have hz : z ∈ innerC i := by
    have h := hzInner.2.2
    change parent i ((parent i).symm z) ∈ innerC i at h
    have ht : z ∈ (parent i).target := houterTarget i (by rwa [hchartTarget i] at hzt)
    simpa only [(parent i).right_inv ht] using h
  exact hsample i hz hyball

#print axioms parameterRound2_exists_compact_prepared_bufferedAtlas
end
end GlobalEmbedding.Continuation
