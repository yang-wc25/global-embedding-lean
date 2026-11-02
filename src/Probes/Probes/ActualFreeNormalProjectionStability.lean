import Probes.ActualFreeNormalProjection
import GlobalEmbedding.Paper.PointwiseJetNormalBound

/-! The actual two-projection normal keeps a uniform nonzero reserve when the
actual first and transverse frames move. The old unit legal vector is fixed
by both old projections; the new reserve is an OUTPUT of the frame bounds. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {N : ℕ} {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_normal_projection_gap_from_gram
    (A0 A : E →L[ℝ] V) (c : ℝ) (hc : 0 < c)
    (hA : ∀ w, c*‖w‖^2 ≤ ‖A0 w‖^2)
    (hSmall : ‖A0-A‖ ≤ Real.sqrt c/2) :
    ‖(LinearMap.range A.toLinearMap)ᗮ.starProjection -
      (LinearMap.range A0.toLinearMap)ᗮ.starProjection‖ ≤
      (3/Real.sqrt c)*‖A0-A‖ := by
  have hh := (pointwise_projected_jet_estimate A0 A
    (ContinuousLinearMap.id ℝ V) (ContinuousLinearMap.id ℝ V)
    c 1 hc hA hSmall ContinuousLinearMap.norm_id_le).2
  simpa only [ContinuousLinearMap.comp_id,sub_self,norm_zero,zero_add,mul_one] using hh

private theorem two_projection_vector_distance
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (QA QA0 QB QB0 : W →L[ℝ] W) (v : W) (hv : ‖v‖ = 1)
    (hQA0 : QA0 v = v) (hQB0 : QB0 v = v)
    (hQB : ∀ w, ‖QB w‖ ≤ ‖w‖) :
    ‖QB (QA v)-v‖ ≤ ‖QA-QA0‖+‖QB-QB0‖ := by
  have hAv : ‖QA v-v‖ ≤ ‖QA-QA0‖ := by
    have hh := (QA-QA0).le_opNorm v
    simpa only [sub_apply,hQA0,hv,mul_one] using hh
  have hBv : ‖QB v-v‖ ≤ ‖QB-QB0‖ := by
    have hh := (QB-QB0).le_opNorm v
    simpa only [sub_apply,hQB0,hv,mul_one] using hh
  have hid : QB (QA v)-v = QB (QA v-v)+(QB v-v) := by rw [map_sub]; abel
  rw [hid]
  calc
    _ ≤ ‖QB (QA v-v)‖+‖QB v-v‖ := norm_add_le _ _
    _ ≤ ‖QA v-v‖+‖QB v-v‖ := add_le_add (hQB (QA v-v)) le_rfl
    _ ≤ ‖QA-QA0‖+‖QB-QB0‖ := add_le_add hAv hBv

theorem actual_free_normal_projection_uniform_reserve
    (cA cB : ℝ) (hcA : 0 < cA) (hcB : 0 < cB) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀
      (A0 A : E →L[ℝ] V) (B0 B : T →L[ℝ] V),
      (∀ w, cA*‖w‖^2 ≤ ‖A0 w‖^2) →
      (∀ w, cB*‖w‖^2 ≤ ‖B0 w‖^2) →
      ‖A0-A‖ ≤ epsilon → ‖B0-B‖ ≤ epsilon →
      ∀ v : V, ‖v‖ = 1 →
      v ∈ (LinearMap.range A0.toLinearMap)ᗮ →
      v ∈ (LinearMap.range B0.toLinearMap)ᗮ →
      (1/2 : ℝ) ≤ ‖actualFreeNormalProjectionRaw A B v‖ := by
  let D : ℝ := 3/Real.sqrt cA + 3/Real.sqrt cB
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let epsilon := min (Real.sqrt cA/2)
    (min (Real.sqrt cB/2) (1/(2*(D+1))))
  have hepsilon : 0 < epsilon := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hSmallA : epsilon ≤ Real.sqrt cA/2 := min_le_left _ _
  have hSmallB : epsilon ≤ Real.sqrt cB/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hCost : D*epsilon ≤ 1/2 := by
    calc
      _ ≤ D*(1/(2*(D+1))) := mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans (min_le_right _ _)) hD
      _ ≤ (D+1)*(1/(2*(D+1))) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1/2 := by field_simp
  refine ⟨epsilon,hepsilon,?_⟩
  intro A0 A B0 B hA hB hAe hBe v hv hvA hvB
  let QA := (LinearMap.range A.toLinearMap)ᗮ.starProjection
  let QA0 := (LinearMap.range A0.toLinearMap)ᗮ.starProjection
  let QB := (LinearMap.range B.toLinearMap)ᗮ.starProjection
  let QB0 := (LinearMap.range B0.toLinearMap)ᗮ.starProjection
  have hQA0 : QA0 v = v := Submodule.starProjection_eq_self_iff.mpr hvA
  have hQB0 : QB0 v = v := Submodule.starProjection_eq_self_iff.mpr hvB
  have hQA : ‖QA-QA0‖ ≤ (3/Real.sqrt cA)*epsilon :=
    (actual_normal_projection_gap_from_gram A0 A cA hcA hA (hAe.trans hSmallA)).trans
      (mul_le_mul_of_nonneg_left hAe (by positivity))
  have hQB : ‖QB-QB0‖ ≤ (3/Real.sqrt cB)*epsilon :=
    (actual_normal_projection_gap_from_gram B0 B cB hcB hB (hBe.trans hSmallB)).trans
      (mul_le_mul_of_nonneg_left hBe (by positivity))
  have hDifference : ‖actualFreeNormalProjectionRaw A B v-v‖ ≤ 1/2 := by
    have hb := two_projection_vector_distance QA QA0 QB QB0 v hv hQA0 hQB0
      (fun w => (LinearMap.range B.toLinearMap)ᗮ.norm_starProjection_apply_le w)
    calc
      _ ≤ ‖QA-QA0‖+‖QB-QB0‖ := hb
      _ ≤ (3/Real.sqrt cA)*epsilon+(3/Real.sqrt cB)*epsilon := add_le_add hQA hQB
      _ = D*epsilon := by dsimp [D]; ring
      _ ≤ 1/2 := hCost
  have hh := norm_sub_norm_le v (actualFreeNormalProjectionRaw A B v)
  rw [norm_sub_rev, hv] at hh
  linarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_normal_projection_gap_from_gram
#print axioms GlobalEmbedding.Continuation.actual_free_normal_projection_uniform_reserve
