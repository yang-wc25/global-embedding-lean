import NormalPolar.OriginalWaveSeedRescaledRawProfiles

/-! Positive reference rescaling transports the exact original partition and
buffers. Their forward/inverse maps and ambient amplitudes do not change. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}

/-- The chart/partition data are selected once from the original map. -/
def OriginalWaveSeedRefinement.rescale
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (c : ℝ) (hc : c ≠ 0) :
    OriginalWaveSeedRefinement (m := m) (c • F) (contMDiff_const_rescale F hF c)
      (actualRescaledLegalWave F hF c hc w) weight where
  count := d.count
  chart := d.chart
  partition := d.partition
  chart_source := d.chart_source
  chart_smooth := d.chart_smooth
  inverse_smooth := d.inverse_smooth
  phase_coordinate := d.phase_coordinate
  inverse_phase := d.inverse_phase
  partition_smooth := d.partition_smooth
  partition_nonneg := d.partition_nonneg
  partition_support := d.partition_support
  partition_one := d.partition_one

variable {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

def OriginalWaveSeedBuffer.rescale (b : OriginalWaveSeedBuffer d i)
    (c : ℝ) (hc : c ≠ 0) : OriginalWaveSeedBuffer (d.rescale c hc) i where
  compactTarget := b.compactTarget
  compact := b.compact
  contained := b.contained
  contains_support := b.contains_support

theorem OriginalWaveSeedBuffer.rescale_chart (b : OriginalWaveSeedBuffer d i)
    (c : ℝ) (hc : c ≠ 0) : (b.rescale c hc).chart = b.chart := rfl

theorem OriginalWaveSeedBuffer.rescale_spatialChart (b : OriginalWaveSeedBuffer d i)
    (c : ℝ) (hc : c ≠ 0) : (b.rescale c hc).spatialChart = b.spatialChart := rfl

theorem OriginalWaveSeedRefinement.rescale_cutoff
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (c : ℝ) (hc : c ≠ 0) (i : Fin d.count) :
    (d.rescale c hc).cutoff i = d.cutoff i := rfl

theorem OriginalWaveSeedRefinement.rescale_cutoffCoordinates
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (c : ℝ) (hc : c ≠ 0) (i : Fin d.count) :
    (d.rescale c hc).cutoffCoordinates i = d.cutoffCoordinates i := rfl

/-- All physical Gram and kernel conditions hold for the same charts and
actual ambient normals at every nonzero reference contraction. -/
def OriginalWaveSeedBuffer.rescaled_physical_geometry
    (b b' : OriginalWaveSeedBuffer d i)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget) (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (c : ℝ) (hc : c ≠ 0) :
    ActualPrescribedPhysicalGeometry (fun _ : Z => c • F)
      (fun _ => contMDiff_const_rescale F hF c)
      (fun _ => b'.spatialChart.symm)
      (fun _ y => actualRescaledNormal F hF c hc (b'.spatialChart.symm y)
        (w.normal (b'.spatialChart.symm y)))
      b.chart (fun z : Z × M => weight * w.phase z.2) :=
  (b.rescale c hc).actual_physical_geometry (b'.rescale c hc) hbb hweight
    (fun x => (immersion_const_rescale_iff F hF c hc x).mpr (hImm x))

/-- The literal reference factor for delta=t^10 lies in the previously
fixed uniform contraction interval. -/
theorem actual_probe_contraction_mem_Icc (t : ℝ) (ht : 0 < t) (htmax : t ≤ 1/2) :
    Real.sqrt (1-(t^(10:ℕ))^2) ∈ Icc (1/2 : ℝ) 1 := by
  have hp : t^(20:ℕ) ≤ (1/2:ℝ)^20 := pow_le_pow_left₀ ht.le htmax 20
  have hid : (t^(10:ℕ))^2 = t^(20:ℕ) := by ring
  have hrad : 0 ≤ 1-(t^(10:ℕ))^2 := by rw [hid]; norm_num at hp ⊢; linarith
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (1-(t^(10:ℕ))^2)
  rw [mem_Icc]
  constructor
  · have hquarter : (t^(10:ℕ))^2 ≤ (1/4:ℝ) := by
      rw [hid]
      norm_num at hp
      linarith
    nlinarith
  · nlinarith [sq_nonneg (t^(10:ℕ))]

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.rescaled_physical_geometry
#print axioms GlobalEmbedding.NormalPolar.actual_probe_contraction_mem_Icc

