import NormalPolar.OriginalWaveSeedGroupedIdentity
import ProbesClosure.GeneralOriginalValue

/-! Exact identity of the original paired response map and the prescribed
wave used by the grouped quadratic construction. Subordinate pieces retain
the same original two parameter coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace GeneralLegalWaveRawFamily

def groupedPairMap (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (u : ProbeParameters r) (x : M) : V :=
  jointGroupedPrescribedWave (round4PairedParameterIndex r).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun l s => fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
    (fun l s => actualProbeNormalAmplitude (fun _ : Z => c • F)
      (fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
      ((family.piece l).seed.cutoffCoordinates s)
      (fun _ y => actualRescaledNormal F hF c (GeneralLegalWaveSeed.contraction_ne_zero c hc)
        (((family.piece l).seed.outer s).chart.symm y) ((waves l).normal (((family.piece l).seed.outer s).chart.symm y)))
      delta tau (weight l))
    (fun l => fun z : Z × M => weight l*(waves l).phase z.2)
    tau length (fun l s => (family.piece l).seed.physicalChart s)
    (probeParameterEmbedding (round4PairedParameterIndex r).toEmbedding u) (default,x)

theorem groupedPairMap_eq_originalPairMap
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ) :
    family.groupedPairMap c hc delta tau length =
      family.originalPairMap c hc delta tau length := by
  funext u x
  unfold groupedPairMap
  rw [originalGroupedPrescribedWave_eq_pair_sum]
  rfl

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.groupedPairMap_eq_originalPairMap

