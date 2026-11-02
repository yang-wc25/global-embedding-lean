import NormalPolar.OriginalWaveSeedRefinement

/-!
# Arbitrary smooth cutoffs: phase-adapted refinement with original labels

The frozen `Upgrade.LocalLegalWave` requires a `SmoothBumpFunction`.
The paper permits an arbitrary smooth cutoff compactly supported in a
coordinate chart. The input below deliberately needs only the open legal
neighborhood of that support. Every paper legal wave supplies these data;
the extra chart assumption is not needed for this construction.

The actual finite adapted cover and ordinary partition are obtained from
the already proved increments theorem. Every piece uses the same original
phase and weight. Summation recovers the original amplitude, and the
double sum of all within-label cross terms is the original squared norm.

This is an upstream general-input construction, not an assertion of the
full probe proposition. The frozen raw-family and response interfaces
still have to be generalized or faithfully transported to this input.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

section Input
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- An arbitrary smooth cutoff with a genuine open legal neighborhood.
No sign, normalization, radial shape, center, or nonvanishing normal is
required. On a compact source its closed support is automatically compact.
The paper's coordinate-chart support premise implies this weaker geometric
entry; proving this entry is consequently sufficient for its refinement. -/
structure OpenSupportedLegalWave (F : M → V)
    (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F) where
  domain : Set M
  phase : M → ℝ
  normal : ∀ x, normalSpace (I := IM) F x
  cutoff : M → ℝ
  cutoff_smooth : ContMDiff IM 𝓘(ℝ,ℝ) ∞ cutoff
  domain_open : IsOpen domain
  support_subset : tsupport cutoff ⊆ domain
  phase_smooth : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase domain
  normal_smooth : ContMDiffOn IM 𝓘(ℝ,V) ∞ (fun x => (normal x : V)) domain
  legal : ∀ x ∈ domain,
    GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x) ∧
      normal x ∈ supportedRankLegalValueSpace (trueSecondForm F hF x)
        (mfderiv IM 𝓘(ℝ,ℝ) phase x).toLinearMap

namespace OpenSupportedLegalWave

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}

def value (w : OpenSupportedLegalWave (n := n) F hF) (x : M) : V :=
  w.cutoff x • (w.normal x : V)

/-- The frozen downstream wave class embeds without changing any phase,
cutoff, or normal field. The reverse conversion is not asserted. -/
def ofLocal [T2Space M] (w : LocalLegalWave (n := n) F hF) :
    OpenSupportedLegalWave (n := n) F hF where
  domain := w.domain
  phase := w.phase
  normal := w.normal
  cutoff := w.cutoff
  cutoff_smooth := w.cutoff.contMDiff
  domain_open := w.domain_open
  support_subset := w.support_subset
  phase_smooth := w.phase_smooth
  normal_smooth := w.normal_smooth
  legal := w.legal

@[simp] theorem ofLocal_value [T2Space M] (w : LocalLegalWave (n := n) F hF) (x : M) :
    (ofLocal w).value x = w.value x := rfl

theorem compact_support [CompactSpace M] (w : OpenSupportedLegalWave (n := n) F hF) :
    IsCompact (tsupport w.cutoff) := (isClosed_tsupport _).isCompact

end OpenSupportedLegalWave
end Input

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- A finite ordinary subdivision of one arbitrary-cutoff legal wave.
Its piece indices never become independent probe-parameter labels. -/
structure GeneralLegalWaveRefinement (F : M → V)
    (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph (Z × M) (Z × D)
  partition : Fin count → Z × M → ℝ
  chart_source : ∀ i, (chart i).source ⊆ univ ×ˢ w.domain
  chart_smooth : ∀ i, ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ,Z) IM)
    𝓘(ℝ,Z × D) ∞ (chart i) (chart i).source
  inverse_smooth : ∀ i, ContMDiffOn 𝓘(ℝ,Z × D)
    (ModelWithCorners.prod 𝓘(ℝ,Z) IM) ∞ (chart i).symm (chart i).target
  phase_coordinate : ∀ i z, z ∈ (chart i).source →
    ((chart i) z).1 = z.1 ∧ ((chart i) z).2 0 = weight * w.phase z.2
  inverse_phase : ∀ i z, z ∈ (chart i).target →
    ((chart i).symm z).1 = z.1 ∧ weight * w.phase ((chart i).symm z).2 = z.2 0
  partition_smooth : ∀ i, ContMDiff (ModelWithCorners.prod 𝓘(ℝ,Z) IM)
    𝓘(ℝ,ℝ) ∞ (partition i)
  partition_nonneg : ∀ i z, 0 ≤ partition i z
  partition_support : ∀ i, tsupport (partition i) ⊆ (chart i).source
  partition_one : ∀ z : Z × M, z.2 ∈ tsupport w.cutoff → ∑ i, partition i z = 1

/-- The finite adapted geometry is produced from the general input, with
no `SmoothBumpFunction` witness or extra global phase chart assumed. -/
theorem exists_generalLegalWaveRefinement
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) (hweight : 0 < weight) :
    Nonempty (GeneralLegalWaveRefinement (m := m) F hF w weight) := by
  classical
  let W : Set (Z × M) := univ ×ˢ univ
  let chi : Z × M → ℝ := fun z => w.cutoff z.2
  let psi : Z × M → ℝ := fun z => weight * w.phase z.2
  let O : Set (Z × M) := univ ×ˢ w.domain
  let A : Set (Z × M) := Subtype.val '' tsupport (fun z : W => chi z.val)
  have hparent : A ⊆ O := by
    rintro z ⟨y,hy,rfl⟩
    have hs := tsupport_comp_subset_preimage w.cutoff
      (continuous_snd.comp (continuous_subtype_val : Continuous (Subtype.val : W → Z × M)))
    exact ⟨mem_univ _,w.support_subset (hs hy)⟩
  have hactive (z : Z × M) (hz : z.2 ∈ tsupport w.cutoff) : z ∈ A := by
    let sectionMap : M → W := fun x => ⟨(z.1,x),by simp [W]⟩
    have hs : Continuous sectionMap :=
      (continuous_const.prodMk continuous_id).subtype_mk _
    have ht := tsupport_comp_subset_preimage (fun y : W => chi y.val) hs
    exact ⟨sectionMap z.2,ht hz,rfl⟩
  have hpsi : ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ,Z) IM) 𝓘(ℝ,ℝ) ∞
      psi (W ∩ O) := by
    exact contMDiffOn_const.mul (w.phase_smooth.comp contMDiff_snd.contMDiffOn
      (fun z hz => hz.2.2))
  have hcritical : ∀ z ∈ A ∩ (univ ×ˢ (univ : Set M)),
      mfderiv IM 𝓘(ℝ,ℝ) (fun x : M => psi (z.1,x)) z.2 ≠ 0 := by
    intro z hz
    have hdom : z.2 ∈ w.domain := (hparent hz.1).2
    have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt
      (by simp)
    have he : mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) z.2 =
        weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase z.2 :=
      (hd.hasMFDerivAt.const_smul weight).mfderiv
    change mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) z.2 ≠ 0
    rw [he]
    exact smul_ne_zero hweight.ne' ((w.legal z.2 hdom).1.1)
  obtain ⟨r,a,L,rho,Lambda,hL,hLc,hAL,hLa,hactiveChart,hcharts,hsub,hsum,
      hLambda,hKL,hLambdaSub,hcover,hretain,hrecover⟩ :=
    increments_exists_finite_adapted_cover_partition_of_mfderiv_ne_zero
      (F := V) (univ : Set Z) isOpen_univ (univ : Set Z) isCompact_univ Subset.rfl
      chi psi O (isOpen_univ.prod w.domain_open) hparent hpsi hcritical
  refine ⟨{
    count := r
    chart := a
    partition := fun i z => rho i z
    chart_source := fun i z hz => ((hcharts i).1 hz).2
    chart_smooth := fun i => (hcharts i).2.1
    inverse_smooth := fun i => (hcharts i).2.2.1
    phase_coordinate := fun i => (hcharts i).2.2.2.1
    inverse_phase := fun i => (hcharts i).2.2.2.2
    partition_smooth := fun i => (rho i).contMDiff
    partition_nonneg := rho.nonneg
    partition_support := hsub
    partition_one := ?_ }⟩
  intro z hz
  exact hsum z (hcover ⟨hactive z hz, hKL (mem_univ _),mem_univ _⟩)

namespace GeneralLegalWaveRefinement

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : OpenSupportedLegalWave (n := m+1) F hF} {weight : ℝ}

def cutoff (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (i : Fin d.count) : Z × M → ℝ := fun z => d.partition i z * w.cutoff z.2

theorem cutoff_smooth (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (i : Fin d.count) :
    ContMDiff (ModelWithCorners.prod 𝓘(ℝ,Z) IM) 𝓘(ℝ,ℝ) ∞ (d.cutoff i) :=
  (d.partition_smooth i).mul (w.cutoff_smooth.comp contMDiff_snd)

theorem cutoff_support (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (i : Fin d.count) :
    tsupport (d.cutoff i) ⊆ (Prod.snd ⁻¹' tsupport w.cutoff) ∩ (d.chart i).source := by
  intro z hz
  have hleft := tsupport_smul_subset_left (d.partition i) (fun z : Z × M => w.cutoff z.2)
  have hright := tsupport_smul_subset_right (d.partition i) (fun z : Z × M => w.cutoff z.2)
  have hpre := tsupport_comp_subset_preimage w.cutoff
    (continuous_snd : Continuous (Prod.snd : Z × M → M))
  exact ⟨hpre (hright hz),d.partition_support i (hleft hz)⟩

theorem sum_cutoff (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (z : Z × M) : ∑ i, d.cutoff i z = w.cutoff z.2 := by
  by_cases hz : z.2 ∈ tsupport w.cutoff
  · simp only [cutoff,← Finset.sum_mul]
    rw [d.partition_one z hz,one_mul]
  · have hzero := image_eq_zero_of_notMem_tsupport (f := w.cutoff) hz
    simp [cutoff,hzero]

/-- One original amplitude, recovered from all subordinate pieces. -/
theorem sum_value (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (z : Z × M) :
    ∑ i, d.cutoff i z • (w.normal z.2 : V) = w.value z.2 := by
  rw [← Finset.sum_smul,d.sum_cutoff]
  rfl

/-- Both quadratures keep the exact same original fast angle on every
piece. This identity has no independent weight or parameter per piece. -/
theorem sum_paired_value (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (z : Z × M) (b : Bool) (tau : ℝ) :
    ∑ i, probeTrig b (weight * w.phase z.2 / tau) •
      (d.cutoff i z • (w.normal z.2 : V)) =
        probeTrig b (weight * w.phase z.2 / tau) • w.value z.2 := by
  rw [← Finset.smul_sum,d.sum_value]

/-- Quadratic extraction keeps every cross term within the original label.
Taking only the diagonal sum of piece squares would not be this identity. -/
theorem all_cross_terms (d : GeneralLegalWaveRefinement (m := m) F hF w weight)
    (z : Z × M) :
    (∑ i, ∑ j, inner ℝ (d.cutoff i z • (w.normal z.2 : V))
      (d.cutoff j z • (w.normal z.2 : V))) = ‖w.value z.2‖ ^ 2 := by
  rw [← d.sum_value z]
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  exact Finset.sum_comm

end GeneralLegalWaveRefinement
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.exists_generalLegalWaveRefinement
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRefinement.sum_value
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRefinement.sum_paired_value
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRefinement.all_cross_terms
