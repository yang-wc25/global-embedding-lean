import Upgrade.CompactFixedAtlasGeometry
import Upgrade.SupportedPhaseTransport
import Upgrade.SupportedActualLocus
import GlobalEmbedding.Offline.BestPhaseLipschitz
import GlobalEmbedding.Paper.LinearSecondFormGoodOpen
import GlobalEmbedding.Paper.SaturationOriginalData
import GlobalEmbedding.Paper.FreeCompactPivotPerturbation

/-!
# Actual phase geometry on the original fixed atlas

The same original good covectors are transported through the proved inverse
chart differential. The fixed projected Hessian is a continuous field, and its
positive best-phase margin is derived from the original phase condition.
No Riemannian metric or uniform moving-chart assumption is added.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology TensorProduct

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section LinearPhase
variable {W Z : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The accepted normalization and least-singular-norm criteria give a
positive actual best-phase value from the original algebraic phase predicate.
This is the existing good-covector argument specialized to a fixed source. -/
theorem bestPhaseSupremum_pos_of_linearPhase
    (hdim : 2 ≤ finrank ℝ W) (S : SymmetricSquare W →L[ℝ] Z)
    (hphase : LinearSecondFormPhaseRegular S.toLinearMap) :
    0 < bestPhaseSupremum S := by
  obtain ⟨ξ, hξ⟩ := (saturation_phaseRegular_iff_continuous_covector S.toLinearMap).mp hphase
  have hξ0 : ξ ≠ 0 := by
    intro hz
    apply hξ.1
    exact congrArg ContinuousLinearMap.toLinearMap hz
  have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
  let η : W →L[ℝ] ℝ := ‖ξ‖⁻¹ • ξ
  have hηnorm : ‖η‖ = 1 := by
    dsimp only [η]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']
  have hη := (linearSecondFormGoodCovector_continuous_smul_iff S.toLinearMap ξ
    ‖ξ‖⁻¹ (inv_ne_zero hp.ne')).mpr hξ
  let : Nontrivial η.ker := covector_kernel_nontrivial hdim η
  let : Nontrivial (SymmetricSquare η.ker) := symmetric_square_nontrivial
  have hi := (linearSecondFormGoodCovector_iff_native_restriction S η).mp hη
  have hs := (least_singular_norm_attainment (E := SymmetricSquare η.ker) (F := Z)
    (covectorRestriction S η)).2.2.mpr hi.2
  exact hs.trans_le ((best_phase_supremum_specification hdim S).2.2.1 η hηnorm)

end LinearPhase

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Exact original phase equivalence in the actual fixed atlas frame. -/
theorem probeAtlasProjectedSecondForm_phase_iff
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    LinearSecondFormPhaseRegular (probeAtlasProjectedSecondForm A F i x).toLinearMap ↔
      LinearSecondFormPhaseRegular
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x) := by
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  let e : E ≃L[ℝ] E := probeAtlasInverseFrameEquiv A hA i x hx
  have he : (probeAtlasFrame A i x).toLinearMap = e.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap
      (probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx).symm
  rw [probeAtlasProjectedSecondForm_eq_trueSecondForm A hA F hF i x hx]
  change LinearSecondFormPhaseRegular
    ((normalSpace (I := IM) F x).subtype.comp
      (B.comp (symmetricSquareLinearMap (probeAtlasFrame A i x).toLinearMap))) ↔ _
  rw [he]
  exact (linearSecondFormPhaseRegular_postcomp_iff _ _ Subtype.val_injective).trans
    (linearSecondFormPhaseRegular_source_coordinates_iff B e)

/-- Positive fixed-coordinate margins on an actual support cover imply the
original global phase predicate, including for a disconnected or empty source. -/
theorem phaseRegular_of_probeAtlas_positive_margin
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hpos : ∀ i x, x ∈ A.support i → 0 < bestPhaseSupremum
      (probeAtlasProjectedSecondForm A F i x)) : PhaseRegular F hF := by
  intro x
  obtain ⟨i, hx⟩ := hcover x
  obtain ⟨ξ, _, hξ⟩ := actual_good_covector_of_positive_bestPhaseSupremum
    (by simpa using hdim) (probeAtlasProjectedSecondForm A F i x) (hpos i x hx)
  have hphase := (probeAtlasProjectedSecondForm_phase_iff A hA F hF i x
    (hA.support_subset i hx)).mp ⟨ξ.toLinearMap, hξ⟩
  obtain ⟨η, hη⟩ := (saturation_phaseRegular_iff_continuous_covector
    (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)).mp hphase
  refine ⟨η, ?_, hη.2⟩
  intro hz
  apply hη.1
  exact congrArg ContinuousLinearMap.toLinearMap hz

/-- Actual fixed-coordinate first jets are continuous on their genuine chart
domain. The chart support is later used only as a compact norm domain. -/
theorem continuousOn_probeAtlasFirstJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (i : Fin A.count) :
    ContinuousOn (probeAtlasFirstJet A F i) (A.chart i).source := by
  have hc := (probeAtlas_fixed_coordinate_smooth A hA F hF i).continuousOn_fderiv_of_isOpen
    (A.chart i).open_target (by simp)
  exact hc.comp (A.chart i).continuousOn (A.chart i).mapsTo

/-- Actual quotient Hessians are continuous on the same fixed domain, by the
accepted continuous Hessian lift applied to the literal second derivative. -/
theorem continuousOn_probeAtlasSecondJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (i : Fin A.count) :
    ContinuousOn (probeAtlasSecondJet A F i) (A.chart i).source := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (F ∘ (A.chart i).symm)) (A.chart i).target :=
    (probeAtlas_fixed_coordinate_smooth A hA F hF i).fderiv_of_isOpen
      (A.chart i).open_target (by simp)
  have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart i).open_target (by simp)
  have hc := h2.comp (A.chart i).continuousOn (A.chart i).mapsTo
  exact (show Continuous (actualHessianLift :
    (E →L[ℝ] E →L[ℝ] V) → (SymmetricSquare E →L[ℝ] V)) from
      ContinuousLinearMap.continuous _).comp_continuousOn hc

/-- Continuity of the actual projected Hessian on each chart is derived from
the actual injective derivative field and the accepted inverse-Gram theorem. -/
theorem continuousOn_probeAtlasProjectedSecondForm
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) (i : Fin A.count) :
    ContinuousOn (probeAtlasProjectedSecondForm A F i) (A.chart i).source := by
  have hfirst : Continuous (fun x : (A.chart i).source ↦ probeAtlasFirstJet A F i x) :=
    (continuousOn_probeAtlasFirstJet A hA F hF i).domRestrict
  have hproj := free_frame_normal_projection_continuous _ hfirst
    (fun x ↦ probeAtlasFirstJet_injective A hA F hF i x x.property (himm x))
  have hsecond : Continuous (fun x : (A.chart i).source ↦ probeAtlasSecondJet A F i x) :=
    (continuousOn_probeAtlasSecondJet A hA F hF i).domRestrict
  exact continuousOn_iff_continuous_domRestrict.mpr (hproj.clm_comp hsecond)

end GlobalEmbedding.Upgrade
