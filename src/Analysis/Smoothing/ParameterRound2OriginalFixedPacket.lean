import Probes.ActualOriginalGivenProfile
import Smoothing.ParameterRound2MeanResidualScaling

/-! The original given-data profile is separated exactly into the actual
map, actual tensor, and the unchanged provided phase/normal/cutoff/linear
and coordinate-transition packet. No produced adapted inverse, correction,
mean or output residual is a field of the fixed packet. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

def parameterRound2_originalFixedPacketProfile
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  max (⨆ nu : Fin Data.primaryCount,
    max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))
      (max (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))
        (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data nu)
          (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))))
    (max (⨆ nu : Fin Data.primaryCount,
      paperAtlasWeighted 0 j ell (incrementsOriginalLinearArgumentCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))
      (max (⨆ nu : Fin Data.primaryCount,
        paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data nu)
          (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))
        (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates Data)
          (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data))))

theorem parameterRound2_originalGivenProfile_eq_map_tensor_packet
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile Data j ell =
      max (paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet))
        (max (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet))
          (parameterRound2_originalFixedPacketProfile Data j ell)) := by
  simp only [actualOriginalGivenInputProfile,incrementsOriginalInputProfileWithLinear,
    incrementsOriginalCoreInputProfile,parameterRound2_originalFixedPacketProfile,max_assoc]

theorem parameterRound2_originalFixedPacketProfile_mono_scale
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell t : ℝ) (hle : ell ≤ t) :
    parameterRound2_originalFixedPacketProfile Data j ell ≤ parameterRound2_originalFixedPacketProfile Data j t := by
  dsimp only [parameterRound2_originalFixedPacketProfile]
  apply max_le_max
  · apply iSup_mono
    intro nu
    exact max_le_max (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _)
      (max_le_max (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _)
        (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _))
  · apply max_le_max
    · exact iSup_mono (fun nu => parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _)
    · exact max_le_max (iSup_mono (fun nu => parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _))
        (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _)

theorem parameterRound2_originalGivenProfile_of_actual_map_tensor
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) (hell1 : ell ≤ 1)
    (Mmap Mtensor Mpacket : ℝ)
    (hmap : paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hmapBound : (paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ Mmap)
    (htensor : paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (htensorBound : (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ Mtensor)
    (hpacket : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hpacketBound : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Mpacket) :
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ max Mmap (max Mtensor Mpacket) := by
  have hp := parameterRound2_originalFixedPacketProfile_mono_scale Data j ell 1 hell1
  have hpf := ne_top_of_le_ne_top hpacket hp
  have hpb := (ENNReal.toReal_mono hpacket hp).trans hpacketBound
  rw [parameterRound2_originalGivenProfile_eq_map_tensor_packet]
  have htp : max (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet))
      (parameterRound2_originalFixedPacketProfile Data j ell) ≠ ⊤ := by
    exact (max_lt (lt_top_iff_ne_top.mpr htensor) (lt_top_iff_ne_top.mpr hpf)).ne
  refine ⟨(max_lt (lt_top_iff_ne_top.mpr hmap) (lt_top_iff_ne_top.mpr htp)).ne,?_⟩
  rw [ENNReal.toReal_max hmap htp,ENNReal.toReal_max htensor hpf]
  exact max_le_max hmapBound (max_le_max htensorBound hpb)

theorem parameterRound2_originalGivenProfile_of_same_scale_map_tensor
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ)
    (Mmap Mtensor Mpacket : ℝ)
    (hmap : paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hmapBound : (paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ Mmap)
    (htensor : paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (htensorBound : (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ Mtensor)
    (hpacket : parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤)
    (hpacketBound : (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ Mpacket) :
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ max Mmap (max Mtensor Mpacket) := by
  have hpf := hpacket
  have hpb := hpacketBound
  rw [parameterRound2_originalGivenProfile_eq_map_tensor_packet]
  have htp : max (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet))
      (parameterRound2_originalFixedPacketProfile Data j ell) ≠ ⊤ := by
    exact (max_lt (lt_top_iff_ne_top.mpr htensor) (lt_top_iff_ne_top.mpr hpf)).ne
  refine ⟨(max_lt (lt_top_iff_ne_top.mpr hmap) (lt_top_iff_ne_top.mpr htp)).ne,?_⟩
  rw [ENNReal.toReal_max hmap htp,ENNReal.toReal_max htensor hpf]
  exact max_le_max hmapBound (max_le_max htensorBound hpb)

#print axioms parameterRound2_originalGivenProfile_eq_map_tensor_packet
#print axioms parameterRound2_originalGivenProfile_of_actual_map_tensor
#print axioms parameterRound2_originalGivenProfile_of_same_scale_map_tensor
end GlobalEmbedding.Continuation
