import Probes.ActualFreeNormalProjection

/-! The actual two-projection construction with a varying reference field.
The reference field's original slow profile is consumed by the genuine
bilinear evaluation. All new-normal profiles are produced, not supplied. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {N : ℕ} {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_unit_free_projection_field_slow_jets
    (j : ℕ) (cA cB MA MB mu Mv : ℝ)
    (hcA : 0 < cA) (hcB : 0 < cB) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hmu : 0 < mu) (hMv : 0 ≤ Mv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
      (A : D → E →L[ℝ] V) (B : D → T →L[ℝ] V) (v : D → V) (O S : Set D)
      (_hO : IsOpen O) (_hSO : S ⊆ O)
      (_hA : ContDiffOn ℝ ∞ A O) (_hB : ContDiffOn ℝ ∞ B O) (_hv : ContDiffOn ℝ ∞ v O)
      (_hAi : ∀ x ∈ O, Function.Injective (A x))
      (_hBi : ∀ x ∈ O, Function.Injective (B x))
      (ell : ℝ) (_hell : 0 < ell),
      (∀ x ∈ S, ∀ w : E, cA*‖w‖^2 ≤ ‖A x w‖^2) →
      (∀ x ∈ S, ∀ w : T, cB*‖w‖^2 ≤ ‖B x w‖^2) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ MA) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k B x‖ ≤ MB) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k v x‖ ≤ Mv) →
      (∀ x ∈ O, LinearMap.range (B x).toLinearMap ≤ (LinearMap.range (A x).toLinearMap)ᗮ) →
      (∀ x ∈ S, mu ≤ ‖actualFreeNormalProjectionRaw (A x) (B x) (v x)‖) →
      let raw := fun x => actualFreeNormalProjectionRaw (A x) (B x) (v x)
      ContDiffOn ℝ ∞ raw O ∧
      ContDiffOn ℝ ∞ (NormedSpace.normalize ∘ raw) (O ∩ raw ⁻¹' ({0}ᶜ : Set V)) ∧
      (∀ x ∈ S, ‖NormedSpace.normalize (raw x)‖ = 1 ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (A x).toLinearMap)ᗮ ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (B x).toLinearMap)ᗮ) ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k (NormedSpace.normalize ∘ raw) x‖ ≤ C := by
  let PA := actualFreeNormalProjectionCost j cA MA
  let PB := actualFreeNormalProjectionCost j cB MB
  let Qb := 2^j*PB*PA
  let Mraw := 2^j*Qb*Mv
  have hPA : 0 ≤ PA := actualFreeNormalProjectionCost_nonneg j hcA hMA
  have hPB : 0 ≤ PB := actualFreeNormalProjectionCost_nonneg j hcB hMB
  have hQb : 0 ≤ Qb := by dsimp [Qb]; positivity
  obtain ⟨C,hC,hUnit⟩ := actual_unit_normalization_slow_jets (N := N) j mu Mraw hmu
  refine ⟨C,hC,?_⟩
  intro D _ _ A B v O S hO hSO hA hB hv hAi hBi ell hell hAr hBr hAj hBj hvj hRange hReserve raw
  let QA := fun x => (LinearMap.range (A x).toLinearMap)ᗮ.starProjection
  let QB := fun x => (LinearMap.range (B x).toLinearMap)ᗮ.starProjection
  obtain ⟨hQA,hQAj⟩ := actual_normal_projection_slow_jets_on_samples A O S hO hSO hA hAi
    j ell cA MA hell hcA hMA hAr hAj
  obtain ⟨hQB,hQBj⟩ := actual_normal_projection_slow_jets_on_samples B O S hO hSO hB hBi
    j ell cB MB hell hcB hMB hBr hBj
  let Q : D → V →L[ℝ] V := fun x => (QB x).comp (QA x)
  have hQ : ContDiffOn ℝ ∞ Q O := hQB.clm_comp hQA
  have hQj : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k Q x‖ ≤ Qb := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ V V V)
      (ContinuousLinearMap.norm_compL_le ℝ V V V) O hO QB QA hQB hQA k ell PB PA hell.le
      hPB x (hSO hx) (fun r hr => hQBj r (hr.trans hk) x hx)
      (fun r hr => hQAj r (hr.trans hk) x hx)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hPB) hPA)
  have hRaw : ContDiffOn ℝ ∞ raw O := hQ.clm_apply hv
  have hRawJets : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k raw x‖ ≤ Mraw := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
      ContinuousLinearMap.norm_id_le O hO Q v hQ hv k ell Qb Mv hell.le hQb x (hSO hx)
      (fun r hr => hQj r (hr.trans hk) x hx) (fun r hr => hvj r (hr.trans hk) x hx)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hQb) hMv)
  obtain ⟨hNorm,hJets⟩ := hUnit O S hO hSO raw hRaw ell hell hReserve hRawJets
  refine ⟨hRaw,?_,?_,hJets⟩
  · exact actual_normalize_contDiffOn.comp (hRaw.mono inter_subset_left) (fun x hx => hx.2)
  · intro x hx
    have hm := actual_free_normal_projection_mem (A x) (B x) (v x) (hRange x (hSO hx))
    exact ⟨hNorm x hx,(LinearMap.range (A x).toLinearMap)ᗮ.smul_mem _ hm.1,
      (LinearMap.range (B x).toLinearMap)ᗮ.smul_mem _ hm.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_unit_free_projection_field_slow_jets
