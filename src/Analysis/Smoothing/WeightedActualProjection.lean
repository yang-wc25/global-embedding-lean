import Smoothing.WeightedActualGram

/-!
# Native slow jets of the actual orthogonal normal projection

The field estimated here is the original orthogonal projection onto the
normal space of the actual frame. Its Gram formula is proved pointwise and
then transferred at the level of germs on the same open joint domain.
Only a fixed singular-value reserve and actual frame jets are inputs.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

section Projection
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A genuine frame reserve implies injectivity of that same frame. -/
theorem actual_frame_injective_of_reserve (A : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hreserve : ∀ v : E, c * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2) : Function.Injective A := by
  intro v w hvw
  have hz : A (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hb := hreserve (v - w)
  simp only [hz, norm_zero, zero_pow (by omega : 2 ≠ 0)] at hb
  have hs : ‖v - w‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by nlinarith [hb])
  have hn : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The true normal projector has the same native weighted derivative bounds
as its actual Gram formula. All parameters may be included in the source D.
The constant contains only j, the reserve c, and the frame jet bound M. -/
theorem actual_normal_projection_slow_jets
    (A : D → E →L[ℝ] F) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (j : ℕ) (ell c M : ℝ)
    (hell : 0 < ell) (hc : 0 < c) (hM : 0 ≤ M)
    (hreserve : ∀ x ∈ O, ∀ v : E, c * ‖v‖ ^ 2 ≤ ‖A x v‖ ^ 2)
    (hjet : ∀ k ≤ j, ∀ x ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => (LinearMap.range (A x).toLinearMap)ᗮ.starProjection) O ∧
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y => (LinearMap.range (A y).toLinearMap)ᗮ.starProjection) x‖ ≤
        1 + 2 ^ j * (2 ^ j * M * slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j) * M := by
  let R := slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j
  have hR : 0 ≤ R := slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le) (by positivity) j
  let B : D → E →L[ℝ] F := fun x => freeGramRightInverse (A x)
  obtain ⟨hB, hBb⟩ := actual_freeGramRightInverse_slow_jets A O hO hA j ell c M
    hell hc hM hreserve hjet
  change ContDiffOn ℝ ∞ B O at hB
  let adj : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjoint) O := adj.contDiff.comp_contDiffOn hA
  have hadjb := actual_adjoint_slow_jets A j ell M O hjet
  let T : D → F →L[ℝ] F := fun x => (B x).comp (A x).adjoint
  have hT : ContDiffOn ℝ ∞ T O := hB.clm_comp hadj
  have hTb : ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k T x‖ ≤ 2 ^ j * (2 ^ j * M * R) * M := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ F E F)
      (ContinuousLinearMap.norm_compL_le ℝ F E F) O hO B (fun y => (A y).adjoint)
      hB hadj k ell (2 ^ j * M * R) M hell.le (by positivity) x hx
      (fun r hr => hBb r (hr.trans hk) x hx) (fun r hr => hadjb r (hr.trans hk) x hx)
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (by positivity)) hM
  let Q : D → F →L[ℝ] F := fun x => ContinuousLinearMap.id ℝ F - T x
  have hQ : ContDiffOn ℝ ∞ Q O := contDiffOn_const.sub hT
  have hQb : ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k Q x‖ ≤ 1 + 2 ^ j * (2 ^ j * M * R) * M := by
    intro k hk x hx
    have hid : ell ^ k * ‖iteratedFDeriv ℝ k
        (fun _ : D => ContinuousLinearMap.id ℝ F) x‖ ≤ 1 := by
      by_cases hk0 : k = 0
      · subst k
        simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
          ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)
      · rw [iteratedFDeriv_const_of_ne hk0]
        simp
    have ht : ContDiffAt ℝ k T x := (hT.contDiffAt (hO.mem_nhds hx)).of_le (by simp)
    have hd := iteratedFDeriv_sub_apply (𝕜 := ℝ)
      (f := fun _ : D => ContinuousLinearMap.id ℝ F) contDiffAt_const ht
    change iteratedFDeriv ℝ k Q x = _ at hd
    rw [hd]
    calc
      _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k (fun _ : D => ContinuousLinearMap.id ℝ F) x‖ +
          ‖iteratedFDeriv ℝ k T x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hell.le k)
      _ = ell ^ k * ‖iteratedFDeriv ℝ k (fun _ : D => ContinuousLinearMap.id ℝ F) x‖ +
          ell ^ k * ‖iteratedFDeriv ℝ k T x‖ := by ring
      _ ≤ 1 + 2 ^ j * (2 ^ j * M * R) * M := add_le_add hid (hTb k hk x hx)
  have hEq : ∀ x ∈ O, (LinearMap.range (A x).toLinearMap)ᗮ.starProjection = Q x := by
    intro x hx
    have hi := actual_frame_injective_of_reserve (A x) c hc (hreserve x hx)
    simpa only [Q, T, B, freeGramRightInverse, ContinuousLinearMap.comp_assoc] using
      (normal_projection_gram_formula (A x) hi).2.2.2
  refine ⟨hQ.congr hEq, ?_⟩
  intro k hk x hx
  have he : (fun y => (LinearMap.range (A y).toLinearMap)ᗮ.starProjection) =ᶠ[𝓝 x] Q :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hx) (fun y hy => hEq y hy)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hQb k hk x hx

end Projection
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_normal_projection_slow_jets
