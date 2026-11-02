import GlobalEmbedding.Paper.IncrementsFiniteAdaptedCoverPartition
import Upgrade.ProbeInterface
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Finite adapted pieces for one arbitrary original legal wave

The original wave need not have a single phase chart covering its support.
The existing original local-chart and finite ordinary-partition constructors
produce actual adapted pieces before any scale or probe parameter is chosen.
All pieces keep the same original phase, weight, normal and parameter label.
Their ordinary sum recovers the original amplitude, retaining cross terms
when the grouped amplitude is later used in the quadratic construction.

Only a one-point seed parameter is used here. Its resulting parameter-open
neighbourhood is the whole seed, so no original probe ball is restricted.
This is a geometric input producer; uniform raw profile and full probe
construction remain separate obligations.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)

/-- Actual finite ordinary subdivision of one supplied legal wave. The
original label is not replaced by independent labels for its pieces. -/
structure OriginalWaveSeedRefinement (F : M → (EuclideanSpace ℝ (Fin N)))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ F) (w : LocalLegalWave (n := m+1) F hF) (weight : ℝ) where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph (Z × M) (Z × (EuclideanSpace ℝ (Fin (m+1))))
  partition : Fin count → Z × M → ℝ
  chart_source : ∀ i, (chart i).source ⊆ univ ×ˢ w.domain
  chart_smooth : ∀ i, ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) 𝓘(ℝ,Z × (EuclideanSpace ℝ (Fin (m+1)))) ∞ (chart i) (chart i).source
  inverse_smooth : ∀ i, ContMDiffOn 𝓘(ℝ,Z × (EuclideanSpace ℝ (Fin (m+1)))) (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) ∞ (chart i).symm (chart i).target
  phase_coordinate : ∀ i z, z ∈ (chart i).source →
    ((chart i) z).1 = z.1 ∧ ((chart i) z).2 0 = weight * w.phase z.2
  inverse_phase : ∀ i z, z ∈ (chart i).target →
    ((chart i).symm z).1 = z.1 ∧ weight * w.phase ((chart i).symm z).2 = z.2 0
  partition_smooth : ∀ i, ContMDiff (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) 𝓘(ℝ,ℝ) ∞ (partition i)
  partition_nonneg : ∀ i z, 0 ≤ partition i z
  partition_support : ∀ i, tsupport (partition i) ⊆ (chart i).source
  partition_one : ∀ z : Z × M, z.2 ∈ tsupport (w.cutoff : M → ℝ) →
    ∑ i, partition i z = 1

/-- The partition and all phase-adapted charts are constructed from the
literal original legal wave. There is no global-support chart premise. -/
theorem exists_originalWaveSeedRefinement
    (F : M → (EuclideanSpace ℝ (Fin N))) (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ F)
    (w : LocalLegalWave (n := m+1) F hF) (weight : ℝ) (hweight : 0 < weight) :
    Nonempty (OriginalWaveSeedRefinement (m := m) F hF w weight) := by
  classical
  let W : Set (Z × M) := univ ×ˢ univ
  let chi : Z × M → ℝ := fun z => w.cutoff z.2
  let psi : Z × M → ℝ := fun z => weight * w.phase z.2
  let O : Set (Z × M) := univ ×ˢ w.domain
  let A : Set (Z × M) := Subtype.val '' tsupport (fun z : W => chi z.val)
  have hparent : A ⊆ O := by
    rintro z ⟨y,hy,rfl⟩
    have hs := tsupport_comp_subset_preimage (w.cutoff : M → ℝ)
      (continuous_snd.comp (continuous_subtype_val : Continuous (Subtype.val : W → Z × M)))
    exact ⟨mem_univ _,w.support_subset (hs hy)⟩
  have hactive (z : Z × M) (hz : z.2 ∈ tsupport (w.cutoff : M → ℝ)) : z ∈ A := by
    let sectionMap : M → W := fun x => ⟨(z.1,x),by simp [W]⟩
    have hs : Continuous sectionMap :=
      (continuous_const.prodMk continuous_id).subtype_mk _
    have ht := tsupport_comp_subset_preimage (fun y : W => chi y.val) hs
    exact ⟨sectionMap z.2,ht hz,rfl⟩
  have hpsi : ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) 𝓘(ℝ,ℝ) ∞ psi (W ∩ O) := by
    exact contMDiffOn_const.mul (w.phase_smooth.comp contMDiff_snd.contMDiffOn
      (fun z hz => hz.2.2))
  have hcritical : ∀ z ∈ A ∩ (univ ×ˢ (univ : Set M)),
      mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,ℝ) (fun x : M => psi (z.1,x)) z.2 ≠ 0 := by
    intro z hz
    have hdom : z.2 ∈ w.domain := (hparent hz.1).2
    have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt
      (by simp)
    have he : mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) z.2 =
        weight • mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,ℝ) w.phase z.2 :=
      (hd.hasMFDerivAt.const_smul weight).mfderiv
    change mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) z.2 ≠ 0
    rw [he]
    exact smul_ne_zero hweight.ne' ((w.legal z.2 hdom).1.1)
  obtain ⟨r,a,L,rho,Lambda,hL,hLc,hAL,hLa,hactiveChart,hcharts,hsub,hsum,
      hLambda,hKL,hLambdaSub,hcover,hretain,hrecover⟩ :=
    increments_exists_finite_adapted_cover_partition_of_mfderiv_ne_zero
      (F := (EuclideanSpace ℝ (Fin N))) (univ : Set Z) isOpen_univ (univ : Set Z) isCompact_univ Subset.rfl
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

namespace OriginalWaveSeedRefinement

variable {F : M → (EuclideanSpace ℝ (Fin N))} {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}

/-- The actual localized cutoff, using the ordinary partition. -/
def cutoff (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) : Z × M → ℝ :=
  fun z => d.partition i z * w.cutoff z.2

theorem cutoff_smooth (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) :
    ContMDiff (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) 𝓘(ℝ,ℝ) ∞ (d.cutoff i) :=
  (d.partition_smooth i).mul (w.cutoff.contMDiff.comp contMDiff_snd)

theorem cutoff_support (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) :
    tsupport (d.cutoff i) ⊆ (Prod.snd ⁻¹' tsupport (w.cutoff : M → ℝ)) ∩ (d.chart i).source := by
  intro z hz
  have hleft := tsupport_smul_subset_left (d.partition i) (fun z : Z × M => w.cutoff z.2)
  have hright := tsupport_smul_subset_right (d.partition i) (fun z : Z × M => w.cutoff z.2)
  have hpre := tsupport_comp_subset_preimage (w.cutoff : M → ℝ)
    (continuous_snd : Continuous (Prod.snd : Z × M → M))
  exact ⟨hpre (hright hz),d.partition_support i (hleft hz)⟩

theorem sum_cutoff (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (z : Z × M) :
    ∑ i, d.cutoff i z = w.cutoff z.2 := by
  by_cases hz : z.2 ∈ tsupport (w.cutoff : M → ℝ)
  · simp only [cutoff,← Finset.sum_mul]
    rw [d.partition_one z hz,one_mul]
  · have hzero := image_eq_zero_of_notMem_tsupport (f := (w.cutoff : M → ℝ)) hz
    simp [cutoff,hzero]

/-- The original normal amplitude is recovered before quadratic extraction.
In particular, the subordinate pieces have a single original parameter label. -/
theorem sum_value (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (z : Z × M) :
    ∑ i, d.cutoff i z • (w.normal z.2 : (EuclideanSpace ℝ (Fin N))) = w.value z.2 := by
  rw [← Finset.sum_smul,d.sum_cutoff]
  rfl

end OriginalWaveSeedRefinement
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_originalWaveSeedRefinement
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.sum_value
