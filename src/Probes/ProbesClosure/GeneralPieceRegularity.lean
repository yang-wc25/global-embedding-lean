import ProbesClosure.GeneralPieceBinding
import NormalPolar.OriginalWaveSeedPrimitiveRegularity

/-! Joint regularity of the literal reconstructed piece follows from its
manufactured raw geometry. No smoothness assumption on the finished wave
or on its parameter responses is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar GlobalEmbedding.Offline
variable {m N r : ℕ} {M : Type*}
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
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace GeneralLegalWaveRawFamily

theorem piecePrimitives (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count) (delta tau : ℝ) :
    GlobalWavePrescribedPrimitives
      (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
      (fun _ : Fin 1 => fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
      (fun _ : Fin 1 => actualProbeNormalAmplitude (fun _ : Z => c • F)
        (fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
        ((family.piece l).seed.cutoffCoordinates s)
        (fun _ y => actualRescaledNormal F hF c (GeneralLegalWaveSeed.contraction_ne_zero c hc)
          (((family.piece l).seed.outer s).chart.symm y) ((waves l).normal (((family.piece l).seed.outer s).chart.symm y)))
        delta tau (weight l))
      (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
      (fun _ : Fin 1 => (family.piece l).seed.physicalChart s)
      univ (fun _ : Fin 1 => (family.piece l).seed.carrier s) := by
  let raw := fun _ : Fin 1 => family.raw c hc l s 3 2 0 le_rfl zero_le_one
  let binding := family.pieceBinding hImm hweight c hc l s 0 0 le_rfl zero_le_one
  apply globalWave_prescribed_primitives_from_raw
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun _ : Fin 1 => fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
    (fun _ : Fin 1 => (family.piece l).seed.cutoffCoordinates s)
    (fun _ : Fin 1 => fun _ y => actualRescaledNormal F hF c (GeneralLegalWaveSeed.contraction_ne_zero c hc)
      (((family.piece l).seed.outer s).chart.symm y) ((waves l).normal (((family.piece l).seed.outer s).chart.symm y)))
    (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
    (fun _ : Fin 1 => (family.piece l).seed.physicalChart s)
    univ (fun _ : Fin 1 => (family.piece l).seed.carrier s) isOpen_univ
    3 2 0 (family.geometryBudget (max 3 2)) (family.cutoffBudget 3) (family.normalBudget 3)
    delta tau (fun _ : Fin 1 => weight l) raw
  intro i
  exact (globalWave_physical_local_phase_smooth _ _ _ _ _ _
    (binding.geometry i) (raw i).chart_smooth).mono inter_subset_right

theorem piecePairMap_chart_joint
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count)
    (delta tau : ℝ) (length : ℕ)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (i : Fin atlas.count) :
    ContDiffOn ℝ ∞
      (fun z : ProbeParameters 1 × D =>
        family.piecePairMap c hc l s delta tau length z.1 ((atlas.chart i).symm z.2))
      (univ ×ˢ (atlas.chart i).target) := by
  exact originalWave_primitive_chart_joint
    (round4PairedParameterIndex 1).toEmbedding _ _ _ _ _ _ _ _
    (family.piecePrimitives hImm hweight c hc l s delta tau)
    tau length (default : Z) (fun _ => mem_univ _) atlas hAtlas univ i

theorem piecePairMap_value_differentiable
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count)
    (delta tau : ℝ) (length : ℕ) (x : M) (u : ProbeParameters 1) :
    DifferentiableAt ℝ (fun v => family.piecePairMap c hc l s delta tau length v x) u := by
  obtain ⟨i,hi⟩ := atlas.cover x
  have hx := atlas.inner_subset i hi
  have hy := (atlas.chart i).map_source hx
  have h := family.piecePairMap_chart_joint hImm hweight c hc l s delta tau length atlas hAtlas i
  have ha := h.contDiffAt
    ((isOpen_univ.prod (atlas.chart i).open_target).mem_nhds
      (show (u,atlas.chart i x) ∈ univ ×ˢ (atlas.chart i).target from ⟨mem_univ _,hy⟩))
  have hd := (ha.comp u (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  simpa only [Function.comp_def,id_eq,(atlas.chart i).left_inv hx] using hd

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.piecePrimitives
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.piecePairMap_chart_joint

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.piecePairMap_value_differentiable

