import GlobalEmbedding.Offline.RepairMetricIdentity

/-! The native repair identity only needs the three actual source derivatives
at the observation point. This permits the true sample neighborhoods of a
constructed increment, without imposing global regularity outside them. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_ambientDerivative_add_at (F U : M → V) (x : M)
    (hF : MDifferentiableAt I 𝓘(ℝ,V) F x) (hU : MDifferentiableAt I 𝓘(ℝ,V) U x) :
    (tangentSpaceCastModel 𝓘(ℝ,V) ((F+U) x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) (F+U) x) =
    (tangentSpaceCastModel 𝓘(ℝ,V) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) F x)+
    (tangentSpaceCastModel 𝓘(ℝ,V) (U x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) U x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun (mfderiv_add hF hU) v

theorem actual_ambientDerivative_sub_at (F U : M → V) (x : M)
    (hF : MDifferentiableAt I 𝓘(ℝ,V) F x) (hU : MDifferentiableAt I 𝓘(ℝ,V) U x) :
    (tangentSpaceCastModel 𝓘(ℝ,V) ((F-U) x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) (F-U) x) =
    (tangentSpaceCastModel 𝓘(ℝ,V) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) F x)-
    (tangentSpaceCastModel 𝓘(ℝ,V) (U x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ,V) U x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun (mfderiv_sub hF hU) v

theorem actual_inducedMetric_add_at (F U : M → V) (x : M)
    (hF : MDifferentiableAt I 𝓘(ℝ,V) F x) (hU : MDifferentiableAt I 𝓘(ℝ,V) U x) :
    inducedMetric (I := I) (F+U) x = inducedMetric (I := I) F x+
      metricCrossTerm (I := I) F U x+inducedMetric (I := I) U x := by
  unfold inducedMetric metricCrossTerm
  rw [actual_ambientDerivative_add_at F U x hF hU]
  ext v w
  simp only [LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,add_apply,
    LinearMap.add_apply,innerₗ_apply_apply,inner_add_left,inner_add_right]
  ring

theorem actual_metricCrossTerm_sub_left_at (G S U : M → V) (x : M)
    (hG : MDifferentiableAt I 𝓘(ℝ,V) G x) (hS : MDifferentiableAt I 𝓘(ℝ,V) S x) :
    metricCrossTerm (I := I) (G-S) U x = metricCrossTerm (I := I) G U x-metricCrossTerm (I := I) S U x := by
  unfold metricCrossTerm
  rw [actual_ambientDerivative_sub_at G S x hG hS]
  ext v w
  simp only [LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,sub_apply,
    LinearMap.add_apply,LinearMap.sub_apply,innerₗ_apply_apply,inner_sub_left,inner_sub_right]
  ring

theorem actual_inducedMetric_update_at (G SG U : M → V) (x : M)
    (hG : MDifferentiableAt I 𝓘(ℝ,V) G x) (hSG : MDifferentiableAt I 𝓘(ℝ,V) SG x)
    (hU : MDifferentiableAt I 𝓘(ℝ,V) U x) :
    inducedMetric (I := I) (G+U) x-inducedMetric (I := I) G x-
      (inducedMetric (I := I) (SG+U) x-inducedMetric (I := I) SG x) =
      metricCrossTerm (I := I) (G-SG) U x := by
  rw [actual_inducedMetric_add_at G U x hG hU,actual_inducedMetric_add_at SG U x hSG hU,
    actual_metricCrossTerm_sub_left_at G SG U x hG hSG]
  abel

theorem actual_repair_normalized_defect_identity_at (G SG U : M → V) (x : M)
    (hG : MDifferentiableAt I 𝓘(ℝ,V) G x) (hSG : MDifferentiableAt I 𝓘(ℝ,V) SG x)
    (hU : MDifferentiableAt I 𝓘(ℝ,V) U x)
    (delta deltaNext : ℝ) (hdelta : delta ≠ 0) (hdeltaNext : deltaNext ≠ 0)
    (hstar h0 SH : LinearMap.BilinForm ℝ (TangentSpace I x)) :
    let H := (delta^2)⁻¹ • (hstar-inducedMetric (I := I) G x)
    let Hnext := (deltaNext^2)⁻¹ • (hstar-inducedMetric (I := I) (G+U) x)
    let error := inducedMetric (I := I) (SG+U) x-inducedMetric (I := I) SG x-
      delta^2 • (SH-(deltaNext/delta)^2 • h0)
    deltaNext^2 • (Hnext-h0) = delta^2 • (H-SH)-error-metricCrossTerm (I := I) (G-SG) U x := by
  intro H Hnext error
  have hid := actual_inducedMetric_update_at G SG U x hG hSG hU
  have hscale : delta^2*(deltaNext/delta)^2 = deltaNext^2 := by field_simp
  ext v w
  have hi := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) => B v w) hid
  simp only [H,Hnext,error,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul] at hi ⊢
  have hd : delta^2 ≠ 0 := pow_ne_zero 2 hdelta
  have hn : deltaNext^2 ≠ 0 := pow_ne_zero 2 hdeltaNext
  field_simp
  nlinarith [hscale]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_normalized_defect_identity_at
