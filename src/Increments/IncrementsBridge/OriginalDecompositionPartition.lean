import GlobalEmbedding.Paper.IncrementsOriginalDecompositionExtension
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility
import GlobalEmbedding.Offline.SquareCutoffNormalization

/-!
# An actual subordinate partition from the given positive decomposition

The original decomposition already forces its actual cutoff family to cover
the original parameter region. This follows from its linear extension on the
same symmetric tensor fiber, rather than an added positivity or cover input.
The existing square-normalization formula then constructs a smooth partition
on that region, preserving each original relative support and every pair.
No source atlas, original cutoff, phase, normal, or norm domain is replaced.

This is an internal partition supplier. It does not claim the separate host
refinement and quantitative original input bounds required by full increments.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The given open-neighborhood decomposition forces a nonzero original
cutoff at each point. No positivity assumption on H is needed. -/
theorem incrementsBridge_original_decomposition_cutoff_cover
    (Data : IncrementsOriginalNativeData n d N M P)
    (hn : 0 < n) (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    ∃ nu, Data.cutoff nu (p,x) ≠ 0 := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let A : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x) :=
    LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
      (EuclideanSpace.proj (0 : Fin n)).toLinearMap (EuclideanSpace.proj (0 : Fin n)).toLinearMap
  have hA : A.IsSymm := ⟨fun v w => mul_comm _ _⟩
  let u : TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x := EuclideanSpace.single (0 : Fin n) 1
  have hpos : 0 < A u u := by
    change 0 < (EuclideanSpace.single (0 : Fin n) (1 : ℝ) 0)*
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ) 0)
    simp
  by_contra hnone
  have hz : ∀ nu, Data.cutoff nu (p,x) = 0 := by simpa using hnone
  have hdec := (incrementsOriginal_decomposition_extension Data hDecomp p hp x).1 ⟨A,hA⟩
  have hzero : A = 0 := by
    simpa only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,zero_smul,
      Finset.sum_const_zero] using hdec
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

theorem incrementsBridge_original_decomposition_square_sum_pos
    (Data : IncrementsOriginalNativeData n d N M P)
    (hn : 0 < n) (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (z : P × M) (hz : z ∈ incrementsOriginalParameterRegion Data) :
    0 < squareCutoffSum Data.cutoff z := by
  classical
  obtain ⟨nu,hnu⟩ := incrementsBridge_original_decomposition_cutoff_cover Data hn hDecomp z.1 hz.1 z.2
  exact (sq_pos_of_ne_zero hnu).trans_le
    (Finset.single_le_sum (fun k _ => sq_nonneg (Data.cutoff k z)) (Finset.mem_univ nu))

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) 𝓘(ℝ,EuclideanSpace ℝ (Fin n))

/-- The original relative support agrees with the ordinary support inside
the original open parameter region. Arbitrary outside values are untouched. -/
theorem incrementsBridge_original_relative_support_eq
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (nu : Fin Data.primaryCount) :
    incrementsOriginalRelativeCutoffSupport Data nu =
      incrementsOriginalParameterRegion Data ∩ tsupport (Data.cutoff nu) := by
  let W := incrementsOriginalParameterRegion Data
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  unfold incrementsOriginalRelativeCutoffSupport
  change Subtype.val '' closure (Subtype.val ⁻¹' Function.support (Data.cutoff nu) : Set W) =
    W ∩ closure (Function.support (Data.cutoff nu))
  rw [← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Function.support (Data.cutoff nu)),Set.image_preimage_eq_inter_range]
  simp only [Subtype.range_coe_subtype,Set.ofPred_mem_eq,Set.inter_comm]

/-- Original local cutoff smoothness plus its original support containment
gives smoothness throughout the original parameter region. -/
theorem incrementsBridge_original_cutoff_joint_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) :
    ContMDiffOn IJ 𝓘(ℝ,ℝ) ∞ (Data.cutoff nu) (incrementsOriginalParameterRegion Data) := by
  intro z hz
  by_cases hsupport : z ∈ tsupport (Data.cutoff nu)
  · have hrelative : z ∈ incrementsOriginalRelativeCutoffSupport Data nu := by
      rw [incrementsBridge_original_relative_support_eq Data hd nu]
      exact ⟨hz,hsupport⟩
    have hlocal : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local nu hrelative,hz⟩
    exact ((hs.cutoff_joint nu).contMDiffAt
      (((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)).mem_nhds hlocal)).contMDiffWithinAt
  · exact contMDiffWithinAt_of_notMem hsupport ∞ _

/-- The original family itself manufactures a smooth square partition, with
the same relative individual supports and therefore the same pair supports. -/
theorem incrementsBridge_original_decomposition_partition
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data) :
    (∀ nu, ContMDiffOn IJ 𝓘(ℝ,ℝ) ∞ (squareNormalizedCutoff Data.cutoff nu)
      (incrementsOriginalParameterRegion Data)) ∧
    (∀ z ∈ incrementsOriginalParameterRegion Data,
      ∑ nu, (squareNormalizedCutoff Data.cutoff nu z)^2 = 1) ∧
    (∀ nu, tsupport (fun z : incrementsOriginalParameterRegion Data =>
      squareNormalizedCutoff Data.cutoff nu z.val) ⊆
      tsupport (fun z : incrementsOriginalParameterRegion Data => Data.cutoff nu z.val)) ∧
    (∀ nu mu, tsupport (fun z : incrementsOriginalParameterRegion Data =>
      squareNormalizedCutoff Data.cutoff nu z.val) ∩
      tsupport (fun z : incrementsOriginalParameterRegion Data =>
        squareNormalizedCutoff Data.cutoff mu z.val) ⊆
      tsupport (fun z : incrementsOriginalParameterRegion Data => Data.cutoff nu z.val) ∩
      tsupport (fun z : incrementsOriginalParameterRegion Data => Data.cutoff mu z.val)) := by
  have hpos := incrementsBridge_original_decomposition_square_sum_pos Data
    (by have hn := hd.source_dim; omega) hDecomp
  have hCut := incrementsBridge_original_cutoff_joint_smooth Data hd hs
  have hSum : ContMDiffOn IJ 𝓘(ℝ,ℝ) ∞ (squareCutoffSum Data.cutoff)
      (incrementsOriginalParameterRegion Data) := by
    unfold squareCutoffSum
    intro z hz
    apply ContMDiffWithinAt.sum
    intro nu _
    have hfun : (fun w => (Data.cutoff nu w)^2) = Data.cutoff nu * Data.cutoff nu := by
      funext w
      exact pow_two (Data.cutoff nu w)
    rw [hfun]
    exact (hCut nu z hz).mul (hCut nu z hz)
  have hrec : ContMDiffOn IJ 𝓘(ℝ,ℝ) ∞
      (reciprocalSquareRoot ∘ squareCutoffSum Data.cutoff)
      (incrementsOriginalParameterRegion Data) := by
    intro z hz
    have hh : ContDiffAt ℝ ∞ reciprocalSquareRoot (squareCutoffSum Data.cutoff z) :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hpos z hz))
    exact hh.comp_contMDiffWithinAt (hSum z hz)
  have hSupport (nu : Fin Data.primaryCount) :
      tsupport (fun z : incrementsOriginalParameterRegion Data =>
        squareNormalizedCutoff Data.cutoff nu z.val) ⊆
      tsupport (fun z : incrementsOriginalParameterRegion Data => Data.cutoff nu z.val) :=
    tsupport_mul_subset_left
  exact ⟨fun nu => (hCut nu).mul hrec,
    fun z hz => squareNormalizedCutoff_sum_sq Data.cutoff z (hpos z hz),hSupport,
    fun nu mu => inter_subset_inter (hSupport nu) (hSupport mu)⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_decomposition_cutoff_cover
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_decomposition_square_sum_pos
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_relative_support_eq
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_cutoff_joint_smooth
#print axioms GlobalEmbedding.Continuation.incrementsBridge_original_decomposition_partition
