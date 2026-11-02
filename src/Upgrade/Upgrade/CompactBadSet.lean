import Upgrade.ProtectionMargins
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# No new compact incidences outside a chosen finite cover

The map in the perturbed zero set is the new map itself.  A compactness argument
produces a strictly positive radius from the old continuous geometric data; the
absence of newly created bad points is not supplied as an input hypothesis.
Relative closed loci are treated in their actual open ambient subtype.
-/

open Set Topology

namespace GlobalEmbedding.Upgrade

section ClosedIncidence

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- A compact closed-incidence exclusion radius.  `Z` may be a relatively
closed locus by taking `Y` to be the full-rank open ambient subtype. -/
theorem compact_no_new_incidence
    {K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U)
    {Z : Set Y} (hZ : IsClosed Z) {Φ : X → Y} (hΦ : ContinuousOn Φ K)
    (hcover : ∀ x ∈ K, Φ x ∈ Z → x ∈ U) :
    ∃ e > 0, ∀ Ψ : X → Y,
      (∀ x ∈ K, dist (Ψ x) (Φ x) < e) →
      ∀ x ∈ K, Ψ x ∈ Z → x ∈ U := by
  rcases Z.eq_empty_or_nonempty with h | hZne
  · exact ⟨1, by norm_num, by simp [h]⟩
  let C := K \ U
  have hC : IsCompact C := hK.diff hU
  have hpos : ∀ x ∈ C, 0 < Metric.infDist (Φ x) Z := by
    intro x hx
    apply (hZ.notMem_iff_infDist_pos hZne).mp
    intro hbad
    exact hx.2 (hcover x hx.1 hbad)
  obtain ⟨e, he, hdist⟩ := compact_positive_lower_bound hC
    ((Metric.continuous_infDist_pt Z).comp_continuousOn
      (hΦ.mono diff_subset)) hpos
  refine ⟨e, he, ?_⟩
  intro Ψ hclose x hx hbad
  by_contra hnot
  have hlt := hdist x ⟨hx, hnot⟩
  have hle : Metric.infDist (Φ x) Z ≤ dist (Ψ x) (Φ x) := by
    simpa only [dist_comm] using Metric.infDist_le_dist_of_mem hbad
  exact (not_lt_of_ge (hle.trans (hclose x hx).le)) hlt

/-- One finite list of neighborhoods is chosen from the actual old incidence
set, and the same list contains **every** incidence for all sufficiently close
new maps.  The list is chosen before the uniform perturbation radius. -/
theorem compact_finite_incidence_cover
    {K : Set X} (hK : IsCompact K) {Z : Set Y} (hZ : IsClosed Z)
    {Φ : X → Y} (hΦ : Continuous Φ) {ι : Type*}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x ∈ K, Φ x ∈ Z → ∃ i, x ∈ U i) :
    ∃ s : Finset ι, ∃ e > 0, ∀ Ψ : X → Y,
      (∀ x ∈ K, dist (Ψ x) (Φ x) < e) →
      ∀ x ∈ K, Ψ x ∈ Z → ∃ i ∈ s, x ∈ U i := by
  classical
  have hbad : IsCompact (K ∩ Φ ⁻¹' Z) := hK.inter_right (hZ.preimage hΦ)
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover U hU (by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx.1 hx.2
    exact mem_iUnion.mpr ⟨i, hi⟩)
  let V := ⋃ i ∈ s, U i
  have hV : IsOpen V := isOpen_biUnion fun i _ ↦ hU i
  obtain ⟨e, he, hstable⟩ := compact_no_new_incidence hK hV hZ hΦ.continuousOn
    (fun x hx hbad ↦ hs ⟨hx, hbad⟩)
  refine ⟨s, e, he, ?_⟩
  intro Ψ hclose x hx hbad
  have hmem := hstable Ψ hclose x hx hbad
  simpa only [V, mem_iUnion, exists_prop] using hmem

end ClosedIncidence

section ActualJointIncidence

variable {M A E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup A] [NormedAddCommGroup E]

/-- Compact exclusion for the literal joint second-form/value map
`(B x, F x - F y)`.  The estimates retain the two global value remainders.
No support or vanishing assertion about the perturbed map is used. -/
theorem compact_no_new_joint_incidence
    {P : Set (M × M)} (hP : IsCompact P) {U : Set (M × M)} (hU : IsOpen U)
    {Z : Set A} (hZ : IsClosed Z) {B : M → A} {F : M → E}
    (hB : Continuous B) (hF : Continuous F)
    (hcover : ∀ z ∈ P, B z.1 ∈ Z → F z.1 = F z.2 → z ∈ U) :
    ∃ e > 0, ∀ (B' : M → A) (G : M → E),
      (∀ z ∈ P, ‖B' z.1 - B z.1‖ < e) →
      (∀ z ∈ P, ‖G z.1 - F z.1‖ < e / 2 ∧
        ‖G z.2 - F z.2‖ < e / 2) →
      ∀ z ∈ P, B' z.1 ∈ Z → G z.1 = G z.2 → z ∈ U := by
  let Φ : M × M → A × E := fun z ↦ (B z.1, F z.1 - F z.2)
  have hΦ : Continuous Φ := (hB.comp continuous_fst).prodMk
    ((hF.comp continuous_fst).sub (hF.comp continuous_snd))
  obtain ⟨e, he, hstable⟩ := compact_no_new_incidence hP hU
    (hZ.prod (isClosed_singleton : IsClosed ({0} : Set E))) hΦ.continuousOn
    (fun z hz hbad ↦ hcover z hz hbad.1 (sub_eq_zero.mp hbad.2))
  refine ⟨e, he, ?_⟩
  intro B' G hB' hG z hz hbad hEq
  apply hstable (fun z ↦ (B' z.1, G z.1 - G z.2)) ?_ z hz
    ⟨hbad, sub_eq_zero.mpr hEq⟩
  intro w hw
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨?_, ?_⟩
  · simpa only [Φ, dist_eq_norm] using hB' w hw
  · change dist (G w.1 - G w.2) (F w.1 - F w.2) < e
    rw [dist_eq_norm]
    have hid : (G w.1 - G w.2) - (F w.1 - F w.2) =
      (G w.1 - F w.1) - (G w.2 - F w.2) := by abel
    rw [hid]
    exact (norm_sub_le _ _).trans_lt (by
      have h1 := (hG w hw).1
      have h2 := (hG w hw).2
      linarith)

end ActualJointIncidence

section FiniteRank

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The genuine finite-dimensional operator rank sublevel is closed.  This
uses Mathlib's openness of the complementary rank lower bound. -/
theorem isClosed_operator_finrank_le (q : ℕ) :
    IsClosed {B : V →L[ℝ] W | Module.finrank ℝ B.range ≤ q} := by
  have heq : {B : V →L[ℝ] W | Module.finrank ℝ B.range ≤ q} =
      {B : V →L[ℝ] W | ((q + 1 : ℕ) : Cardinal) ≤ B.toLinearMap.rank}ᶜ := by
    ext B
    change Module.finrank ℝ B.range ≤ q ↔
      ¬((q + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ B.range
    rw [← Module.finrank_eq_rank]
    norm_cast
    omega
  rw [heq]
  exact (isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := V) (F := W) (q + 1)).isClosed_compl

/-- The actual low-rank coincidence set is compact; phase regularity may be
used separately to identify `rank ≤ q` with `rank = q`. -/
theorem isCompact_lowRank_coincidence
    {M E : Type*} [TopologicalSpace M] [TopologicalSpace E] [T2Space E]
    {P : Set (M × M)} (hP : IsCompact P)
    {B : M → V →L[ℝ] W} (hB : Continuous B) {F : M → E} (hF : Continuous F)
    (q : ℕ) :
    IsCompact {z ∈ P | Module.finrank ℝ (B z.1).range ≤ q ∧ F z.1 = F z.2} := by
  exact hP.inter_right
    (((isClosed_operator_finrank_le q).preimage (hB.comp continuous_fst)).inter
      (isClosed_eq (hF.comp continuous_fst) (hF.comp continuous_snd)))

end FiniteRank

end GlobalEmbedding.Upgrade
