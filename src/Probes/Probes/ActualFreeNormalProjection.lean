import Probes.ActualUnitNormalSlowJets

/-! Actual free-normal preparation from the first and transverse frames.
The raw field is the composition of their two genuine orthogonal projections
applied to a fixed ambient vector. Its normalized value is unit and orthogonal
to both ranges. All slow jets are produced from the frame reserves and input
jets, with a constant chosen before the fields, domain and scale. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {N : ℕ} {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
local notation "V" => EuclideanSpace ℝ (Fin N)

def actualFreeNormalProjectionRaw (A : E →L[ℝ] V) (B : T →L[ℝ] V) (v : V) : V :=
  (LinearMap.range B.toLinearMap)ᗮ.starProjection
    ((LinearMap.range A.toLinearMap)ᗮ.starProjection v)

theorem actual_free_normal_projection_mem
    (A : E →L[ℝ] V) (B : T →L[ℝ] V) (v : V)
    (hRange : LinearMap.range B.toLinearMap ≤ (LinearMap.range A.toLinearMap)ᗮ) :
    actualFreeNormalProjectionRaw A B v ∈ (LinearMap.range A.toLinearMap)ᗮ ∧
    actualFreeNormalProjectionRaw A B v ∈ (LinearMap.range B.toLinearMap)ᗮ := by
  refine ⟨?_,(LinearMap.range B.toLinearMap)ᗮ.starProjection_apply_mem _⟩
  unfold actualFreeNormalProjectionRaw
  rw [Submodule.starProjection_orthogonal]
  change (LinearMap.range A.toLinearMap)ᗮ.starProjection v -
    (LinearMap.range B.toLinearMap).starProjection
      ((LinearMap.range A.toLinearMap)ᗮ.starProjection v) ∈ _
  exact (LinearMap.range A.toLinearMap)ᗮ.sub_mem
    ((LinearMap.range A.toLinearMap)ᗮ.starProjection_apply_mem _)
    (hRange ((LinearMap.range B.toLinearMap).starProjection_apply_mem _))

def actualFreeNormalProjectionCost (j : ℕ) (c M : ℝ) : ℝ :=
  1 + 2^j*(2^j*M*slowInverseMajorant c⁻¹ (2^j*M^2) j)*M

theorem actualFreeNormalProjectionCost_nonneg (j : ℕ) {c M : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) : 0 ≤ actualFreeNormalProjectionCost j c M := by
  have hInv : 0 ≤ slowInverseMajorant c⁻¹ ((2 : ℝ)^j * M^2) j :=
    slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le)
      (mul_nonneg (pow_nonneg (by norm_num) j) (sq_nonneg M)) j
  unfold actualFreeNormalProjectionCost
  exact add_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
      (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j) hM) hInv)) hM)

theorem actual_unit_free_projection_slow_jets
    (j : ℕ) (cA cB MA MB mu Bv : ℝ)
    (hcA : 0 < cA) (hcB : 0 < cB) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hmu : 0 < mu) (hBv : 0 ≤ Bv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
      (A : D → E →L[ℝ] V) (B : D → T →L[ℝ] V) (O S : Set D)
      (_hO : IsOpen O) (_hSO : S ⊆ O)
      (_hA : ContDiffOn ℝ ∞ A O) (_hB : ContDiffOn ℝ ∞ B O)
      (_hAi : ∀ x ∈ O, Function.Injective (A x))
      (_hBi : ∀ x ∈ O, Function.Injective (B x))
      (ell : ℝ) (_hell : 0 < ell),
      (∀ x ∈ S, ∀ w : E, cA*‖w‖^2 ≤ ‖A x w‖^2) →
      (∀ x ∈ S, ∀ w : T, cB*‖w‖^2 ≤ ‖B x w‖^2) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ MA) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k B x‖ ≤ MB) →
      (∀ x ∈ O, LinearMap.range (B x).toLinearMap ≤ (LinearMap.range (A x).toLinearMap)ᗮ) →
      ∀ (v : V), ‖v‖ ≤ Bv →
      (∀ x ∈ S, mu ≤ ‖actualFreeNormalProjectionRaw (A x) (B x) v‖) →
      let raw := fun x => actualFreeNormalProjectionRaw (A x) (B x) v
      ContDiffOn ℝ ∞ raw O ∧
      ContDiffOn ℝ ∞ (NormedSpace.normalize ∘ raw) (O ∩ raw ⁻¹' ({0}ᶜ : Set V)) ∧
      (∀ x ∈ S, ‖NormedSpace.normalize (raw x)‖ = 1 ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (A x).toLinearMap)ᗮ ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (B x).toLinearMap)ᗮ) ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k (NormedSpace.normalize ∘ raw) x‖ ≤ C := by
  let PA := actualFreeNormalProjectionCost j cA MA
  let PB := actualFreeNormalProjectionCost j cB MB
  let Qb := 2^j*PB*PA
  let Mraw := Bv*Qb
  have hPA : 0 ≤ PA := actualFreeNormalProjectionCost_nonneg j hcA hMA
  have hPB : 0 ≤ PB := actualFreeNormalProjectionCost_nonneg j hcB hMB
  have hQb : 0 ≤ Qb := by dsimp [Qb]; positivity
  have hMraw : 0 ≤ Mraw := mul_nonneg hBv hQb
  obtain ⟨C,hC,hUnit⟩ := actual_unit_normalization_slow_jets (N := N) j mu Mraw hmu
  refine ⟨C,hC,?_⟩
  intro D _ _ A B O S hO hSO hA hB hAi hBi ell hell hAr hBr hAj hBj hRange v hv hReserve raw
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
  have hRaw : ContDiffOn ℝ ∞ raw O := hQ.clm_apply contDiffOn_const
  have hRawJets : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k raw x‖ ≤ Mraw := by
    intro k hk x hx
    have heval := norm_iteratedFDeriv_clm_apply_const (hQ.contDiffAt (hO.mem_nhds (hSO hx)))
      (n := k) (c := v) (by simp)
    calc
      _ ≤ ell^k*(‖v‖*‖iteratedFDeriv ℝ k Q x‖) :=
        mul_le_mul_of_nonneg_left heval (pow_nonneg hell.le k)
      _ = ‖v‖*(ell^k*‖iteratedFDeriv ℝ k Q x‖) := by ring
      _ ≤ ‖v‖*Qb := mul_le_mul_of_nonneg_left (hQj k hk x hx) (norm_nonneg v)
      _ ≤ Bv*Qb := mul_le_mul_of_nonneg_right hv hQb
  obtain ⟨hNorm,hJets⟩ := hUnit O S hO hSO raw hRaw ell hell hReserve hRawJets
  refine ⟨hRaw,?_,?_,hJets⟩
  · exact actual_normalize_contDiffOn.comp (hRaw.mono inter_subset_left) (fun x hx => hx.2)
  · intro x hx
    have hm := actual_free_normal_projection_mem (A x) (B x) v (hRange x (hSO hx))
    exact ⟨hNorm x hx,(LinearMap.range (A x).toLinearMap)ᗮ.smul_mem _ hm.1,
      (LinearMap.range (B x).toLinearMap)ᗮ.smul_mem _ hm.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_free_normal_projection_mem
#print axioms GlobalEmbedding.Continuation.actual_unit_free_projection_slow_jets
