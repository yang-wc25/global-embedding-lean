import Probes.Round3PreparedSymmetricSurjection
import Probes.ActualIncrementGoodPhaseGeometry
import Probes.Round3PreparedStableFrames

/-! The actual stable transverse frame implies the original algebraic
GoodCovector condition. This is the reverse direction needed for a repaired
stage: no new Good/Gram certificate is left as an external input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation
variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round3_prepared_good_of_transverse_frame
    (F : M → Ey) (hF : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ F)
    (chart : OpenPartialHomeomorph M D) (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target)
    (hFrame : Function.Injective (incrementsModeAmbientTransverseFrame F hF chart.symm x)) :
    GoodCovector F hF (chart.symm x)
      ((EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x))) := by
  let A : D ≃L[ℝ] TangentSpace 𝓙 (chart.symm x) := actualIncrementChartDerivativeEquiv chart hchart x hx
  let xi := (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x))
  let e : D0 ≃ₗ[ℝ] xi.ker := {
    toFun := fun v => ⟨A (actualIncrementZeroInsert m v),by
      change (A.symm (A (actualIncrementZeroInsert m v))) 0 = 0
      rw [A.symm_apply_apply]
      rfl⟩
    invFun := fun w => actualIncrementTail m (A.symm w)
    map_add' := by intro v w; apply Subtype.ext; simp only [map_add,Submodule.coe_add]
    map_smul' := by intro a v; apply Subtype.ext; simp only [map_smul,Submodule.coe_smul,RingHom.id_apply]
    left_inv := by
      intro v
      change actualIncrementTail m (A.symm (A (actualIncrementZeroInsert m v))) = v
      rw [A.symm_apply_apply,actualIncrementTail_zeroInsert]
    right_inv := by
      intro w
      apply Subtype.ext
      change A (actualIncrementZeroInsert m (actualIncrementTail m (A.symm w))) = w
      rw [actualIncrementZeroInsert_tail m (A.symm w) (by exact w.property)]
      exact A.apply_symm_apply w }
  let B := (trueSecondForm F hF (chart.symm x)).comp (symmetricSquareLinearMap xi.ker.subtype)
  have he (a : Fin m) : ((e (EuclideanSpace.single a 1)) : TangentSpace 𝓙 (chart.symm x)) =
      incrementsModeCoordinateDirections chart.symm x a.succ :=
    by
      change A (actualIncrementZeroInsert m (EuclideanSpace.single a 1)) = _
      rw [actualIncrementZeroInsert_single]
      rfl
  have hne : xi ≠ 0 := by
    intro hzero
    have hone : xi (A (EuclideanSpace.single 0 1)) = 1 := by
      change (A.symm (A (EuclideanSpace.single 0 1))) 0 = 1
      rw [A.symm_apply_apply]
      simp
    simpa only [hzero,ContinuousLinearMap.zero_apply,zero_ne_one] using hone
  have hValue (t : Tdata) :
      (B (symmetricSquareLinearMap e.toLinearMap (actualIncrementSortedSymmetricLinear m t)) : Ey) =
        incrementsModeAmbientTransverseFrame F hF chart.symm x t := by
    rw [actualIncrementSortedSymmetricLinear_apply]
    simp only [map_sum,map_smul,Submodule.coe_sum,Submodule.coe_smul]
    unfold incrementsModeAmbientTransverseFrame
    simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    change (trueSecondForm F hF (chart.symm x)
      (symmetricSquareLinearMap xi.ker.subtype
        (symmetricSquareLinearMap e.toLinearMap
          (symmetricSquareProduct D0 (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1)))) : Ey) = _
    rw [round3_prepared_symmetric_map_product,round3_prepared_symmetric_map_product]
    change (trueSecondForm F hF (chart.symm x)
      (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x))
        ((e (EuclideanSpace.single q.val.1 1)) : TangentSpace 𝓙 (chart.symm x))
        ((e (EuclideanSpace.single q.val.2 1)) : TangentSpace 𝓙 (chart.symm x))) : Ey) = _
    rw [he,he]
    rfl
  refine ⟨hne,?_⟩
  change Function.Injective B
  have hSurj := (round3_prepared_symmetric_equiv_surjective e).comp
    (round3_prepared_sorted_symmetric_surjective m)
  intro u v huv
  obtain ⟨a,ha⟩ := hSurj u
  obtain ⟨b,hb⟩ := hSurj v
  dsimp only [Function.comp_def] at ha hb
  have hab : a = b := hFrame (by
    rw [← hValue a,← hValue b]
    rw [ha,hb,huv])
  rw [← ha,← hb,hab]

theorem round3_prepared_good_of_transverse_reserve
    (F : M → Ey) (hF : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ F)
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : ∀ v : Tdata, cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF chart.symm x v‖^2) :
    GoodCovector F hF (chart.symm x)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))) := by
  rw [actual_increment_phaseCovector_eq_chosen_chart psi chart hchart O hO hOt x hx hpsi hadapt]
  exact round3_prepared_good_of_transverse_frame F hF chart hchart x (hOt hx)
    (actual_first_frame_injective_of_reserve _ cT hcT hFrame)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_good_of_transverse_frame
#print axioms GlobalEmbedding.Continuation.round3_prepared_good_of_transverse_reserve
