import NormalPolar.OriginalWaveSeedPrimitives
import Mathlib.Topology.Homeomorph.Lemmas

/-! Remove only the one-point auxiliary seed from the actually constructed
adapted chart. The resulting source chart lies in the original maximal atlas,
keeps the entire localized cutoff support, and retains the exact weighted
original phase in both directions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

private theorem seedSection {X : Type*} [TopologicalSpace X] (x : X) :
    (Homeomorph.uniqueProd Z X).symm x = (default,x) := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · simpa only [Homeomorph.coe_uniqueProd] using (Homeomorph.uniqueProd Z X).apply_symm_apply x

def spatialChart (b : OriginalWaveSeedBuffer d i) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))) :=
  (Homeomorph.uniqueProd Z M).symm.toOpenPartialHomeomorph.trans
    (b.chart.trans (Homeomorph.uniqueProd Z (EuclideanSpace ℝ (Fin (m+1)))).toOpenPartialHomeomorph)

theorem spatialChart_apply (b : OriginalWaveSeedBuffer d i) (x : M) :
    b.spatialChart x = (b.chart (default,x)).2 := by
  simp only [spatialChart,OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply,seedSection,Homeomorph.coe_uniqueProd]

theorem spatialChart_inverse (b : OriginalWaveSeedBuffer d i)
    (y : EuclideanSpace ℝ (Fin (m+1))) :
    b.spatialChart.symm y = (b.chart.symm (default,y)).2 := by
  simp only [spatialChart,OpenPartialHomeomorph.coe_trans_symm,Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply,Homeomorph.symm_symm,
    seedSection,Homeomorph.coe_uniqueProd]

theorem spatialChart_source (b : OriginalWaveSeedBuffer d i) (x : M) :
    x ∈ b.spatialChart.source ↔ (default,x) ∈ b.chart.source := by
  simp [spatialChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,Homeomorph.toOpenPartialHomeomorph_apply,seedSection]

theorem spatialChart_target (b : OriginalWaveSeedBuffer d i)
    (y : EuclideanSpace ℝ (Fin (m+1))) :
    y ∈ b.spatialChart.target ↔ (default,y) ∈ b.chart.target := by
  simp [spatialChart,OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,Homeomorph.toOpenPartialHomeomorph_symm_apply,seedSection]

theorem spatialChart_smooth (b : OriginalWaveSeedBuffer d i) :
    ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ b.spatialChart b.spatialChart.source := by
  have hi : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) ∞
      (fun x : M => ((default : Z),x)) := contMDiff_const.prodMk contMDiff_id
  have heq : (b.spatialChart : M → EuclideanSpace ℝ (Fin (m+1))) =
      fun x => (b.chart (default,x)).2 := funext b.spatialChart_apply
  rw [heq]
  exact (ContinuousLinearMap.snd ℝ Z (EuclideanSpace ℝ (Fin (m+1)))).contMDiff.comp_contMDiffOn
    (b.chart_smooth.comp hi.contMDiffOn (fun x hx => (b.spatialChart_source x).mp hx))

theorem spatialChart_inverse_smooth (b : OriginalWaveSeedBuffer d i) :
    ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ b.spatialChart.symm b.spatialChart.target := by
  have hi : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,Z × EuclideanSpace ℝ (Fin (m+1))) ∞
      (fun y : EuclideanSpace ℝ (Fin (m+1)) => ((default : Z),y)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  have heq : (b.spatialChart.symm : EuclideanSpace ℝ (Fin (m+1)) → M) =
      fun y => (b.chart.symm (default,y)).2 := funext b.spatialChart_inverse
  rw [heq]
  exact contMDiff_snd.comp_contMDiffOn (b.inverse_smooth.comp hi.contMDiffOn
    (fun y hy => (b.spatialChart_target y).mp hy))

theorem spatialChart_maximal (b : OriginalWaveSeedBuffer d i) :
    b.spatialChart ∈ IsManifold.maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M :=
  (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
    ⟨b.spatialChart_smooth,b.spatialChart_inverse_smooth⟩

theorem spatialChart_source_original (b : OriginalWaveSeedBuffer d i) :
    b.spatialChart.source ⊆ w.domain := by
  intro x hx
  exact (d.chart_source i (b.chart_source_subset ((b.spatialChart_source x).mp hx))).2

theorem spatialChart_phase (b : OriginalWaveSeedBuffer d i) (x : M)
    (hx : x ∈ b.spatialChart.source) :
    b.spatialChart x 0 = weight * w.phase x := by
  rw [b.spatialChart_apply]
  exact (b.phase_coordinate (default,x) ((b.spatialChart_source x).mp hx)).2

theorem spatialChart_inverse_phase (b : OriginalWaveSeedBuffer d i)
    (y : EuclideanSpace ℝ (Fin (m+1))) (hy : y ∈ b.spatialChart.target) :
    weight * w.phase (b.spatialChart.symm y) = y 0 := by
  rw [b.spatialChart_inverse]
  exact (b.inverse_phase (default,y) ((b.spatialChart_target y).mp hy)).2

theorem spatialChart_cutoff_support (b : OriginalWaveSeedBuffer d i) :
    tsupport (fun x : M => d.cutoff i (default,x)) ⊆ b.spatialChart.source := by
  intro x hx
  apply (b.spatialChart_source x).mpr
  exact b.cutoff_support
    (tsupport_comp_subset_preimage (d.cutoff i) (continuous_const.prodMk continuous_id) hx)

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.spatialChart_maximal
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.spatialChart_cutoff_support
