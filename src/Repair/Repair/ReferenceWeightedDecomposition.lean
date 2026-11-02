import Repair.ReferenceWeightedNativeData

/-!
# Exact original tensor reconstruction after the actual phase hierarchy

The same native phase and linear tensor-functional rescaling preserve the
literal cutoff/square-root reconstruction on the original parameter-open
region.  The identity holds for every tensor argument, including arguments
outside the positive neighborhood; only the unchanged cutoff supports need
the actual phase differential.  It then yields all original qualitative
positive-decomposition clauses for the weighted native datum.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))

theorem repair_reference_weighted_decomposition_tensor
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hweight : ∀ nu, 0 < weight nu)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M)
    (A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) :
    incrementsOriginalDecompositionTensor (repairReferenceWeightedData Data weight) p x A =
      incrementsOriginalDecompositionTensor Data p x A := by
  classical
  unfold incrementsOriginalDecompositionTensor
  apply Finset.sum_congr rfl
  intro nu _
  by_cases hzero : Data.cutoff nu (p,x) = 0
  · simp only [repairReferenceWeightedData,hzero,zero_mul,zero_pow (by decide : 2 ≠ 0),zero_smul]
  have hregion : (p,x) ∈ incrementsOriginalParameterRegion Data := ⟨hp,mem_univ x⟩
  have hsupport : (p,x) ∈ incrementsOriginalRelativeCutoffSupport Data nu :=
    ⟨⟨(p,x),hregion⟩,subset_tsupport
      (fun y : incrementsOriginalParameterRegion Data => Data.cutoff nu y.val) hzero,rfl⟩
  have hCov := repair_reference_weighted_covector Data weight hd hs nu (p,x)
    ⟨hd.cutoff_support_local nu hsupport,hregion⟩
  have hsqrt : Real.sqrt ((weight nu^2)⁻¹ * Data.linearArgument nu p x A) =
      Real.sqrt (Data.linearArgument nu p x A)/weight nu := by
    rw [mul_comm,← div_eq_mul_inv,Real.sqrt_div' _ (sq_nonneg _),Real.sqrt_sq (hweight nu).le]
  ext v w
  change (Data.cutoff nu (p,x)*Real.sqrt ((weight nu^2)⁻¹*Data.linearArgument nu p x A))^2 *
      (incrementsOriginalPhaseCovector (repairReferenceWeightedData Data weight) nu p x v *
        incrementsOriginalPhaseCovector (repairReferenceWeightedData Data weight) nu p x w) =
    (Data.cutoff nu (p,x)*Real.sqrt (Data.linearArgument nu p x A))^2 *
      (incrementsOriginalPhaseCovector Data nu p x v * incrementsOriginalPhaseCovector Data nu p x w)
  rw [hsqrt,hCov]
  change (Data.cutoff nu (p,x)*(Real.sqrt (Data.linearArgument nu p x A)/weight nu))^2 *
      ((weight nu*incrementsOriginalPhaseCovector Data nu p x v) *
        (weight nu*incrementsOriginalPhaseCovector Data nu p x w)) = _
  field_simp [(hweight nu).ne']
  <;> ring

theorem repair_reference_weighted_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hweight : ∀ nu, 0 < weight nu)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hD : IncrementsOriginalQualitativeDecompositionInputs Data) :
    IncrementsOriginalQualitativeDecompositionInputs (repairReferenceWeightedData Data weight) where
  fiber_open := hD.fiber_open
  H_symmetric := hD.H_symmetric
  reference_symmetric := hD.reference_symmetric
  H_mem := hD.H_mem
  reference_mem := hD.reference_mem
  decomposition := by
    intro p hp x A hA
    rw [repair_reference_weighted_decomposition_tensor Data weight hweight hd hs p hp x A.val]
    exact hD.decomposition p hp x A hA
  argument_positive := by
    intro p hp x nu hcut A hA
    exact mul_pos (inv_pos.mpr (sq_pos_of_pos (hweight nu)))
      (hD.argument_positive p hp x nu hcut A hA)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_decomposition_tensor
#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_decomposition
