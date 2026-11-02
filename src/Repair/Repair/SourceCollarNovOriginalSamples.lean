import Repair.SourceCollarNovParameterLocalization
import Smoothing.ParameterRound2TensorGermSpace
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs

/-! Compactness of the unchanged original evaluation sets and membership of
the actual target tensor in the original germ space.  No Hausdorff assumption
on P is added.  The original raw preparation protects the compact parameter
set by genuine chart-supported unit functions, which proves that set closed.
The coordinate samples are then closed subsets of the original compact
Omega/Q products.  No sample set, differentiation domain or tensor changes. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The original local unit preparation supplies the separation needed for
its compact K.  T1 follows from the charted-space structure; T2 is not used. -/
theorem sourceCollarNov_parameter_set_isClosed
    {ι : Type*} [Fintype ι] (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K : Set P) (hK : IsCompact K)
    {BP TP : ℕ → ℝ} {Dp : ℕ} (RP : TensorLocalRawPreparation B K BP TP Dp) :
    IsClosed K := by
  letI : T1Space P := ChartedSpace.t1Space Ep P
  rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro p hp
  have hKU : K ⊆ ({p} : Set P)ᶜ := by
    intro q hq hqp
    have he : q = p := mem_singleton_iff.mp hqp
    exact hp (he ▸ hq)
  obtain ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hSupport,hRange⟩ :=
    sourceCollarNov_parameter_localization B hB K ({p} : Set P)ᶜ hK
      isOpen_compl_singleton hKU RP
  have hZero : psi p = 0 := image_eq_zero_of_notMem_tsupport
    (fun hz => hSupport hz (mem_singleton p))
  have hOpen : IsOpen {q : P | psi q < (1/2 : ℝ)} :=
    isOpen_lt hPsi.continuous continuous_const
  have hpSmall : p ∈ {q : P | psi q < (1/2 : ℝ)} := by
    change psi p < (1/2 : ℝ)
    rw [hZero]
    norm_num
  apply mem_of_superset (hOpen.mem_nhds hpSmall)
  intro q hq hqK
  have he : psi q = 1 := hOne (hKV hqK)
  change psi q < (1/2 : ℝ) at hq
  rw [he] at hq
  norm_num at hq

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

theorem sourceCollarNov_original_evaluation_compact
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    {BP TP : ℕ → ℝ} {Dp : ℕ}
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i)) :
    ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) := by
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hK : IsClosed Data.parameterSet :=
    sourceCollarNov_parameter_set_isClosed B hB Data.parameterSet hd.parameter_compact RP
  intro i
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain univ i
  let f : (Fin (n+d) → ℝ) → P :=
    fun y => (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).1
  have hS : IsCompact S := parameterRound2_originalEvaluation_univ_compact
    Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain
    hOmega hQ hd.source_norm_subset hd.parameter_norm_subset i
  have hCont : ContinuousOn f S :=
    (parameterRound2_originalJointPoint_continuousOn Data.atlas Data.parameterChart i).fst.mono
      (fun _ hy => hy.1)
  have hClosed : IsClosed (S ∩ f ⁻¹' Data.parameterSet) :=
    hCont.preimage_isClosed_of_isClosed hS.isClosed hK
  have heq : incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i =
        S ∩ f ⁻¹' Data.parameterSet := by
    ext y
    simp only [S,f,incrementsOriginalEvaluation,mem_setOf_eq,mem_inter_iff,mem_preimage,
      mem_univ,and_true]
    tauto
  rw [heq]
  exact hS.of_isClosed_subset hClosed inter_subset_left

/-- The original H itself is a germ-space element.  Its smooth open
neighborhood is precisely the original parameter region in each original
coordinate domain; symmetry is the original decomposition input. -/
theorem sourceCollarNov_original_target_germ_mem
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (W : Set (P × M)) (hW : W ⊆ incrementsOriginalParameterRegion Data) :
    Data.H ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) W := by
  constructor
  · intro i
    let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart i
    let U := O ∩ (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹'
      incrementsOriginalParameterRegion Data
    have hU : IsOpen U :=
      (parameterRound2_originalJointPoint_continuousOn Data.atlas Data.parameterChart i).isOpen_inter_preimage
        (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i)
        (hd.parameter_open.prod isOpen_univ)
    exact ⟨U,hU,fun _ hy => ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩,
      hs.H_coordinates i⟩
  · intro z hz
    exact hDecomp.H_symmetric z.1 (hW hz).1 z.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parameter_set_isClosed
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_evaluation_compact
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_target_germ_mem
