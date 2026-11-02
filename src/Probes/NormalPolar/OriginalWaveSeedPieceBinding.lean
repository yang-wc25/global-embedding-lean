import NormalPolar.OriginalWaveSeedPieceGeometry
import NormalPolar.OriginalWaveSeedSupportedRaw

/-! The actual rescaled legal-wave family supplies the entire primitive
binding used by the original two-channel response theorem for each piece.
Every field is derived from the same finite partition, inner/outer charts,
raw sample, original phase, and unchanged ambient normal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

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
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedRescaledFamily

def pieceBinding (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.refinement l).count)
    (length : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) :
    GlobalWaveSupportedProbeBinding
      (fun _ : Fin 1 => (waves l).phase)
      (fun _ : Fin 1 => (family.refinement l).pieceValue s)
      (fun _ : Fin 1 => (family.refinement l).pieceCarrier s)
      (fun _ : Fin 1 => (family.inner l s).spatialChart)
      (fun _ : Fin 1 => weight l)
      (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
      (fun _ : Fin 1 => fun _ : Z => (family.outer l s).spatialChart.symm)
      (fun _ : Fin 1 => (family.refinement l).cutoffCoordinates s)
      (fun _ : Fin 1 => fun _ y => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
        ((family.outer l s).spatialChart.symm y) ((waves l).normal ((family.outer l s).spatialChart.symm y)))
      (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
      (fun _ : Fin 1 => (family.inner l s).chart)
      univ (fun _ : Fin 1 => tsupport ((family.refinement l).cutoff s))
      ell (family.geometryBudget (max (2+length+1) 2))
      (family.cutoffBudget (2+length+1)) (family.normalBudget (2+length+1))
      (fun _ : Fin 1 => family.raw c hc l s (2+length+1) 2 ell hell hell1) (default : Z) where
  geometry := fun _ => (family.inner l s).rescaled_physical_geometry (family.outer l s)
    (family.nested l s) (hweight l) hImm c (originalWave_contraction_ne_zero c hc)
  source_inside := fun _ => subset_univ _
  coordinates := fun _ y _ => (family.inner l s).spatial_inverse_eq (family.outer l s) y
  target := fun _ y hy => ((family.inner l s).spatialChart_target y).mp hy
  phase_original := fun _ y hy => (family.inner l s).piece_phase_binding (hweight l) y hy
  amplitude_original := fun _ y _ => (family.inner l s).piece_amplitude_binding (family.outer l s)
    c (originalWave_contraction_ne_zero c hc) y
  samples := by
    intro _ x hx
    rw [family.raw_sample]
    exact ((family.inner l s).spatialChart_target _).mp
      ((family.inner l s).spatialChart.map_source
        ((family.inner l s).spatialChart_cutoff_support hx))
  slice := fun _ => mem_univ _
  carrier := fun _ _ hz => (family.refinement l).pieceCarrier_projection s hz

/-- This is the complete reconstructed two-channel wave of this actual
piece. It will be evaluated on the two original coordinates of its label,
so no subordinate index is added to the global parameter space. -/
def piecePairMap (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.refinement l).count)
    (delta tau : ℝ) (length : ℕ) (u : ProbeParameters 1) (x : M) : V :=
  round4PrescribedGlobalWave (round4PairedParameterIndex 1).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun _ : Fin 1 => fun _ : Z => (family.outer l s).spatialChart.symm)
    (fun _ : Fin 1 => actualProbeNormalAmplitude (fun _ : Z => c • F)
      (fun _ : Z => (family.outer l s).spatialChart.symm)
      ((family.refinement l).cutoffCoordinates s)
      (fun _ y => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
        ((family.outer l s).spatialChart.symm y) ((waves l).normal ((family.outer l s).spatialChart.symm y)))
      delta tau (weight l))
    (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
    tau length (fun _ : Fin 1 => (family.inner l s).chart)
    (probeParameterEmbedding (round4PairedParameterIndex 1).toEmbedding u) (default,x)

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.pieceBinding
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.piecePairMap

