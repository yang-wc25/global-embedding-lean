import FaithfulCollars.LocalRefinedRawPreparation

/-!
# Original parameter cover to an actual buffered local family

The given chart maps and Q_i are retained literally.  A point of K needs
an owner chart with a genuine inward norm-domain buffer.  From the compact
set K and an interior cover we first prove the existence of one common
positive buffer.  With a fixed buffer, the working local family is explicit
and its entire sampling set is proved to lie in the ORIGINAL Q_i.

The compactness argument chooses a radius AFTER the particular chart/Q/K
geometry.  It does not exchange this with uniformity over arbitrary atlas
classes.  A fixed numerical setup uses the second construction at its
fixed radius.  The old arbitrary-set `parameter_cover` does not imply an
interior cover unless original openness or an original buffer is supplied.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P]

def OriginalParameterBallCover (chart : ι → OpenPartialHomeomorph P E)
    (Q : ι → Set E) (K : Set P) (b : ℝ) : Prop :=
  ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∧ ball (chart i p) b ⊆ Q i

private theorem finite_positive_lower {α : Type*} (s : Finset α) (r : α → ℝ)
    (hr : ∀ a ∈ s, 0 < r a) : ∃ b > 0, ∀ a ∈ s, b ≤ r a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨b, hb, hs⟩ := ih (fun c hc => hr c (Finset.mem_insert_of_mem hc))
    refine ⟨min b (r a), lt_min hb (hr a (Finset.mem_insert_self _ _)), ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs c hc)

/-- An actual common coordinate buffer from compact K and the original
interior cover.  This theorem has pointwise-geometry quantifier order. -/
theorem originalParameterBallCover_of_compact_interior_cover
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (K : Set P) (hK : IsCompact K)
    (hcover : ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∧ chart i p ∈ interior (Q i)) :
    ∃ b > 0, OriginalParameterBallCover chart Q K b := by
  classical
  have hLocal (p : K) : ∃ i, p.val ∈ (chart i).source ∧
      ∃ r > 0, ball (chart i p.val) (4*r) ⊆ Q i := by
    obtain ⟨i, hi, hQi⟩ := hcover p.val p.property
    obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hQi
    refine ⟨i, hi, e/4, by positivity, ?_⟩
    have heq : 4*(e/4) = e := by ring
    rw [heq]
    exact hball.trans interior_subset
  choose owner hsource radius hradius hball using hLocal
  let U (p : K) : Set P := (chart (owner p)).source ∩
    chart (owner p) ⁻¹' ball (chart (owner p) p.val) (radius p)
  have hU (p : K) : IsOpen (U p) := (chart (owner p)).isOpen_inter_preimage isOpen_ball
  have hpU (p : K) : p.val ∈ U p :=
    ⟨hsource p, by simpa only [Set.mem_preimage, mem_ball, dist_self] using hradius p⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU
    (fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩, hpU ⟨p,hp⟩⟩)
  obtain ⟨b, hb, hbr⟩ := finite_positive_lower s radius (fun p _ => hradius p)
  refine ⟨b, hb, ?_⟩
  intro p hp
  obtain ⟨q, hqs, hpq⟩ := mem_iUnion₂.mp (hs hp)
  refine ⟨owner q, hpq.1, ?_⟩
  intro y hy
  apply hball q
  have hpq' : dist (chart (owner q) p) (chart (owner q) q.val) < radius q := hpq.2
  have hy' : dist y (chart (owner q) p) < b := hy
  change dist y (chart (owner q) q.val) < 4 * radius q
  linarith [dist_triangle y (chart (owner q) p) (chart (owner q) q.val), hbr q hqs, hradius q]

/-- If the original Q_i are open, the old cover field supplies the interior
cover without adding any desired raw output as an assumption. -/
theorem originalParameterBallCover_of_compact_open_cover
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (K : Set P) (hK : IsCompact K) (hQ : ∀ i, IsOpen (Q i))
    (hcover : ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∧ chart i p ∈ Q i) :
    ∃ b > 0, OriginalParameterBallCover chart Q K b := by
  apply originalParameterBallCover_of_compact_interior_cover chart Q K hK
  intro p hp
  obtain ⟨i, hi, hQi⟩ := hcover p hp
  exact ⟨i, hi, by simpa only [(hQ i).interior_eq] using hQi⟩

def originalParameterBufferCore (Q : Set E) (b : ℝ) : Set E :=
  {c | ball c b ⊆ Q}

def originalParameterBufferedInner (Q : Set E) (b : ℝ) : Set E :=
  ⋃ c ∈ originalParameterBufferCore Q b, ball c (b/4)

def originalParameterNormSupport
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E) (i : ι) : Set P :=
  (chart i).source ∩ chart i ⁻¹' Q i

def originalBufferedParameterFamily
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) :
    TensorBufferedChartFamily ι P E where
  chart := chart
  inner i := (chart i).source ∩ chart i ⁻¹' originalParameterBufferedInner (Q i) b
  inner_open i := (chart i).isOpen_inter_preimage (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball)
  inner_subset _ := inter_subset_left
  buffer := b/4
  buffer_pos := by positivity
  buffered := by
    intro i p hp y hy
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp hp.2
    apply hQtarget i
    apply hc
    have hpc' : dist (chart i p) c < b/4 := hpc
    have hy' : dist y (chart i p) < b/4 := hy
    change dist y c < b
    linarith [dist_triangle y (chart i p) c]

theorem originalBufferedParameterFamily_chart_eq
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) :
    (originalBufferedParameterFamily chart Q b hb hQtarget).chart = chart := rfl

theorem originalBufferedParameterFamily_cover
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target)
    (K : Set P) (hcover : OriginalParameterBallCover chart Q K b) :
    ∀ p ∈ K, ∃ i, p ∈ (originalBufferedParameterFamily chart Q b hb hQtarget).inner i := by
  intro p hp
  obtain ⟨i, hi, hQi⟩ := hcover p hp
  exact ⟨i, hi, mem_iUnion₂.mpr ⟨chart i p, hQi, by
    simpa only [mem_ball, dist_self] using (by positivity : 0 < b/4)⟩⟩

variable [Fintype ι]

theorem originalBufferedParameterFamily_sampling
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) (i : ι) :
    tensorLocalSamplingCoordinates (originalBufferedParameterFamily chart Q b hb hQtarget) i ⊆ Q i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzdom := hzInner.2.2
  change chart i ((chart i).symm z) ∈ originalParameterBufferedInner (Q i) b at hzdom
  rw [(chart i).right_inv hzInner.1] at hzdom
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzdom
  apply hc
  have hzc' : dist z c < b/4 := hzc
  have hy' : dist y z < b/4 := hyball
  change dist y c < b
  linarith [dist_triangle y z c]

theorem originalBufferedParameterFamily_inner_radius
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target)
    (R : ℝ) (hR : ∀ i y, y ∈ Q i → ‖y‖ ≤ R) :
    ∀ i y, y ∈ tensorLocalInner (originalBufferedParameterFamily chart Q b hb hQtarget) i → ‖y‖ ≤ R := by
  intro i y hy
  exact hR i y (originalBufferedParameterFamily_sampling chart Q b hb hQtarget i
    (tensorLocalInner_subset_sampling _ i hy))

variable [FiniteDimensional ℝ E] [T2Space P] [ChartedSpace E P] [IsManifold 𝓘(ℝ, E) ∞ P]

theorem originalBufferedParameterFamily_enlarged
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) :
    OriginalLocalBufferedEnlargedSupports (originalBufferedParameterFamily chart Q b hb hQtarget)
      (originalParameterNormSupport chart Q) (b/4) := by
  intro i p hp hnear
  obtain ⟨z, hz, hpz⟩ := hnear
  have hzdom := hz.2.2
  change chart i ((chart i).symm z) ∈ originalParameterBufferedInner (Q i) b at hzdom
  rw [(chart i).right_inv hz.1] at hzdom
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzdom
  refine ⟨hp, hc ?_⟩
  have hzc' : dist z c < b/4 := hzc
  have hpz' : dist (chart i p) z ≤ (b/4)/4 := hpz
  change dist (chart i p) c < b
  linarith [dist_triangle (chart i p) z c]

end GlobalEmbedding.Continuation.FaithfulCollars
