import Repair.EndpointOriginalPrimaryRegularity
import Smoothing.ParameterRound2OriginalFixedPacket

/-! The actual original fixed packet is the maximum of its six literal
components. This assembly retains the original cumulative weighted norms
and their true domains; in particular there is no factor for chart or
primary count. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem repair_ennreal_le_of_actual_bound {a : ℝ≥0∞} {K : ℝ}
    (hFinite : a ≠ ⊤) (hBound : a.toReal ≤ K) : a ≤ ENNReal.ofReal K := by
  rw [← ENNReal.ofReal_toReal hFinite]
  exact ENNReal.ofReal_le_ofReal hBound

theorem repair_original_fixed_packet_components
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hCutoff : ∀ nu, paperAtlasWeighted 0 j 1 (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤ ENNReal.ofReal K)
    (hNormal : ∀ nu, paperAtlasWeighted 0 j 1 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤ ENNReal.ofReal K)
    (hSpatial : ∀ nu, paperAtlasWeighted 0 j 1 (incrementsOriginalPhaseCovectorCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤ ENNReal.ofReal K)
    (hLinear : ∀ nu, paperAtlasWeighted 0 j 1 (incrementsOriginalLinearArgumentCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤ ENNReal.ofReal K)
    (hTotal : ∀ nu, paperAtlasWeighted 0 j 1 (actualOriginalTotalPhaseCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤ ENNReal.ofReal K)
    (hTransition : paperAtlasWeighted 0 j 1 (actualOriginalGivenTransitionDifferentialCoordinates Data)
      (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data) ≤ ENNReal.ofReal K) :
    parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤ ∧
      (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ K := by
  have hb : parameterRound2_originalFixedPacketProfile Data j 1 ≤ ENNReal.ofReal K := by
    exact max_le (iSup_le (fun nu => max_le (hCutoff nu) (max_le (hNormal nu) (hSpatial nu))))
      (max_le (iSup_le hLinear) (max_le (iSup_le hTotal) hTransition))
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb,?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hK)

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem repair_original_cutoff_normal_linear_norms
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hl : IncrementsOriginalLinearSmoothInputs Data) (hOpen : Data.parameterOpen = univ)
    (Cutoff Normal Linear : ℕ → ℝ)
    (hCutoff : ∀ j, 0 ≤ Cutoff j) (hNormal : ∀ j, 0 ≤ Normal j) (hLinear : ∀ j, 0 ≤ Linear j)
    (hCutoffJets : ∀ nu i k y, y ∈ incrementsOriginalPrimaryEvaluation Data nu i →
      ‖iteratedFDeriv ℝ k (incrementsOriginalScalarCoordinates Data (Data.cutoff nu) i) y‖ ≤ Cutoff k)
    (hNormalJets : ∀ nu i k y, y ∈ incrementsOriginalPrimaryEvaluation Data nu i →
      ‖iteratedFDeriv ℝ k (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu) i) y‖ ≤ Normal k)
    (hLinearJets : ∀ nu i k y, y ∈ incrementsOriginalPrimaryEvaluation Data nu i →
      ‖iteratedFDeriv ℝ k (incrementsOriginalLinearArgumentCoordinates Data nu i) y‖ ≤ Linear k)
    (nu : Fin Data.primaryCount) (j : ℕ) :
    (paperAtlasWeighted 0 j 1 (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j 1 (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu)).toReal ≤
          (j+1)*repairOriginalJetPrefix Cutoff j) ∧
    (paperAtlasWeighted 0 j 1 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j 1 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu)).toReal ≤
          (j+1)*repairOriginalJetPrefix Normal j) ∧
    (paperAtlasWeighted 0 j 1 (incrementsOriginalLinearArgumentCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j 1 (incrementsOriginalLinearArgumentCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu)).toReal ≤
          (j+1)*repairOriginalJetPrefix Linear j) := by
  have hO := actual_original_primaryDifferentiation_open Data hd.primary_open nu
  have hSO : ∀ i, incrementsOriginalPrimaryEvaluation Data nu i ⊆ incrementsOriginalPrimaryDifferentiation Data nu i :=
    fun _ _ hy => ⟨hy.1.1,hy.2⟩
  have hLSmooth (i) : ContDiffOn ℝ ∞ (incrementsOriginalLinearArgumentCoordinates Data nu i)
      (incrementsOriginalPrimaryDifferentiation Data nu i) := by
    simpa only [incrementsOriginalParameterRegion,hOpen,univ_prod_univ,preimage_univ,inter_univ] using hl.linear_coordinates nu i
  exact ⟨repair_original_weighted_profile_from_jets _ _ _ hO hSO
      (repair_original_primary_cutoff_smooth Data hd hs hOpen nu) Cutoff hCutoff (hCutoffJets nu) j,
    repair_original_weighted_profile_from_jets _ _ _ hO hSO
      (repair_original_primary_normal_smooth Data hd hs hOpen nu) Normal hNormal (hNormalJets nu) j,
    repair_original_weighted_profile_from_jets _ _ _ hO hSO hLSmooth Linear hLinear (hLinearJets nu) j⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_fixed_packet_components
#print axioms GlobalEmbedding.Continuation.repair_original_cutoff_normal_linear_norms
