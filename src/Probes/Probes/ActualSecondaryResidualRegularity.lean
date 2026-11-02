import Probes.ActualSecondaryResidualRows

/-!
# Actual reduced residual regularity in the joint parameter domain

The spatial derivative inside the original reduced operator is the genuine
slice derivative. Its smoothness follows from the native spatial restriction
bridge, so mixed parameter derivatives are retained. This is an internal
consumer of the already constructed actual finite solution, with no new
regularity premise on a physical residual or desired remainder.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m + 1) → ℂ

theorem actual_joint_reduced_operator_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (u : X → Cdata) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexReducedOperator
      (F z.1) (hF z.1) (c z.1) (fun x => u (z.1, x)) z.2) O := by
  have hdu := (incrementsJointSpatialJets_bridge u O hO hu).2.1
  apply ((hB.clm_apply hu).add (hA.clm_apply hdu)).congr
  intro z hz
  apply incrementsModeComplexReducedOperator_first_order
  have hslice : ContDiffOn ℝ ∞ (fun x : D => u (z.1, x))
      ((fun x : D => (z.1, x)) ⁻¹' O) :=
    hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)
  exact (hslice.contDiffAt
    ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)

theorem actual_joint_reduced_residual_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (u k : X → Cdata) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hu : ContDiffOn ℝ ∞ u O) (hk : ContDiffOn ℝ ∞ k O) (alpha : ℂ) :
    ContDiffOn ℝ ∞ (fun z : X => alpha⁻¹ • u z + incrementsModeComplexReducedOperator
      (F z.1) (hF z.1) (c z.1) (fun x => u (z.1, x)) z.2 - k z) O :=
  ((hu.const_smul alpha⁻¹).add
    (actual_joint_reduced_operator_contDiffOn F hF c u O hO hA hB hu)).sub hk

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_reduced_operator_contDiffOn
#print axioms GlobalEmbedding.Continuation.actual_joint_reduced_residual_contDiffOn
