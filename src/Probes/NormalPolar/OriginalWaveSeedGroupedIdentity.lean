import NormalPolar.OriginalWaveSeedSourceReindex
import NormalPolar.OriginalWaveSeedOriginalValue
import NormalPolar.JointSecondaryGroupedAmplitude

/-! Exact identity of the original paired response map and the prescribed
wave used by the grouped quadratic construction. Subordinate pieces retain
the same original two parameter coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation GlobalEmbedding.Upgrade

section General
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem originalGroupedPrescribedWave_eq_pair_sum
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (u : ProbeParameters r) (z : Ep × M) :
    jointGroupedPrescribedWave label F hF c vf phase tau length a
        (probeParameterEmbedding label u) z =
      ∑ l, ∑ s, round4PrescribedGlobalWave
        (round4PairedParameterIndex 1).toEmbedding F hF
        (fun _ : Fin 1 => c l s) (fun _ : Fin 1 => vf l s)
        (fun _ : Fin 1 => phase l) tau length (fun _ : Fin 1 => a l s)
        (probeParameterEmbedding (round4PairedParameterIndex 1).toEmbedding
          (originalProbePairProjection l u)) z := by
  rw [jointGroupedPrescribedWave_eq_piece_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro s _
  simp only [round4PrescribedGlobalWave,Fin.sum_univ_one]
  rw [originalPrescribedGlobalAmplitude_pair_projection false label l,
    originalPrescribedGlobalAmplitude_pair_projection true label l]
end General

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
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace OriginalWaveSeedRescaledFamily

def groupedPairMap (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (u : ProbeParameters r) (x : M) : V :=
  jointGroupedPrescribedWave (round4PairedParameterIndex r).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun l s => fun _ : Z => (family.outer l s).spatialChart.symm)
    (fun l s => actualProbeNormalAmplitude (fun _ : Z => c • F)
      (fun _ : Z => (family.outer l s).spatialChart.symm)
      ((family.refinement l).cutoffCoordinates s)
      (fun _ y => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
        ((family.outer l s).spatialChart.symm y) ((waves l).normal ((family.outer l s).spatialChart.symm y)))
      delta tau (weight l))
    (fun l => fun z : Z × M => weight l*(waves l).phase z.2)
    tau length (fun l s => (family.inner l s).chart)
    (probeParameterEmbedding (round4PairedParameterIndex r).toEmbedding u) (default,x)

theorem groupedPairMap_eq_originalPairMap
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ) :
    family.groupedPairMap c hc delta tau length =
      family.originalPairMap c hc delta tau length := by
  funext u x
  unfold groupedPairMap
  rw [originalGroupedPrescribedWave_eq_pair_sum]
  rfl

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.originalGroupedPrescribedWave_eq_pair_sum
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.groupedPairMap_eq_originalPairMap

