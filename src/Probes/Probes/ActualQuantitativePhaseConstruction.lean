import Probes.ActualQuantitativePhaseBounds

/-!
# Constructed phase charts from original native jets, with uniform constants

One actual chart works for every observation order. Its source radius is a fixed
multiple of ell determined only by the original first/second phase bounds and
the noncritical spatial directional reserve. No adapted inverse, transition,
chart radius, or inverse higher-jet budget is an input.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology NNReal
namespace GlobalEmbedding.Continuation

variable {Ep Et : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et] [CompleteSpace Et]

/-- This is a local quantitative construction in the genuine joint model.
The original derivative reserve is on a spatial direction; parameters are
preserved literally, while all estimates differentiate every joint direction. -/
theorem actual_exists_uniform_quantitative_phase_chart_all_scales
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : Ep × (ℝ × Et) → ℝ) (z0 : Ep × (ℝ × Et)) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (haxis : mu ≤ |fderiv ℝ psi z0 (0,(1,0))|)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell * ‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph (Ep × (ℝ × Et)) (Ep × (ℝ × Et)),
      a.source = ball z0 (ell/(4*actualPhaseInverseConstant mu M*(1+M))) ∧
      (a : (Ep × (ℝ × Et)) → (Ep × (ℝ × Et))) = actualPhaseCoordinateMap psi ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2.1) ∧
      closedBall (actualPhaseCoordinateMap psi z0)
        ((ell/(4*actualPhaseInverseConstant mu M*(1+M)))/(4*actualPhaseInverseConstant mu M))
          ⊆ a.target ∧
      (∀ y ∈ a.target, ‖fderiv ℝ a.symm y‖ ≤ 2*actualPhaseInverseConstant mu M) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i * ‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualInverseChartMajorant (slowInverseMajorant (2*actualPhaseInverseConstant mu M) Mj j) j) := by
  let B := actualPhaseInverseConstant mu M
  have hB1 : 1 ≤ B := actualPhaseInverseConstant_one_le hmu hM
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hBM : 1 ≤ B*mu := by
    have he : B*mu = mu+1+M := by
      dsimp only [B,actualPhaseInverseConstant]
      field_simp
      ring
    rw [he]
    linarith
  let c : ℝ≥0 := ⟨1/(4*B),by positivity⟩
  let r := ell/(4*B*(1+M))
  have hden : 0 < 4*B*(1+M) := by positivity
  have hr : 0 < r := div_pos hell hden
  have hrle : r ≤ ell := by
    apply (div_le_iff₀ hden).mpr
    have hd : 1 ≤ 4*B*(1+M) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd hell.le]
  have hsub : ball z0 r ⊆ ball z0 ell := ball_subset_ball hrle
  have hcmu : (c:ℝ) ≤ mu/4 := by
    change 1/(4*B) ≤ mu/4
    apply (div_le_iff₀ (by positivity : 0 < 4*B)).mpr
    nlinarith
  have hcaxis : (c:ℝ) < |fderiv ℝ psi z0 (0,(1,0))| :=
    (hcmu.trans_lt (by linarith)).trans_le haxis
  have ha : fderiv ℝ psi z0 (0,(1,0)) ≠ 0 :=
    abs_pos.mp (hmu.trans_le haxis)
  let L := actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha
  have hNL : ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖ ≤ B :=
    actual_phase_inverse_constant_bound mu M hmu hM _ haxis (hfirst z0 (mem_ball_self hell)) ha
  have hNpos : 0 < ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖ := L.symm.norm_pos
  have hNinv : 1/B ≤ ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hNpos hNL
  have hgap : 1/(2*B) ≤ ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖⁻¹-(c:ℝ) := by
    have hnum : 1/(2*B) ≤ 1/B-1/(4*B) := by
      field_simp
      nlinarith
    exact hnum.trans (sub_le_sub_right hNinv _)
  have hcReal : (c:ℝ) < ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖⁻¹ := by
    have hp : 0 < 1/(2*B) := by positivity
    linarith
  have hc : c < ‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹ := by
    exact_mod_cast hcReal
  have hosc : ∀ z ∈ ball z0 r, ‖fderiv ℝ psi z-fderiv ℝ psi z0‖ ≤ (c:ℝ) := by
    intro z hz
    have h2 : ∀ x ∈ ball z0 ell, ‖iteratedFDeriv ℝ 2 psi x‖ ≤ M/ell := by
      intro x hx
      exact (le_div_iff₀ hell).mpr (by simpa only [mul_comm] using hsecond x hx)
    have ho := actual_native_derivative_oscillation psi z0 ell (M/ell) hell hpsi h2 z (hsub hz)
    have hzR : ‖z-z0‖ ≤ r := (show ‖z-z0‖ < r from by simpa only [mem_ball,dist_eq_norm] using hz).le
    have he : (M/ell)*r = (1/(4*B))*(M/(1+M)) := by
      dsimp only [r]
      field_simp
    calc
      _ ≤ (M/ell)*r := ho.trans (mul_le_mul_of_nonneg_left hzR (div_nonneg hM hell.le))
      _ = (1/(4*B))*(M/(1+M)) := he
      _ ≤ c := mul_le_of_le_one_right (by positivity)
        ((div_le_one₀ (by positivity : 0 < 1+M)).mpr (by linarith))
  obtain ⟨a,hs,hfun,hAs,hAis,hid,_hlip,hfirstInv,htarget⟩ :=
    actual_quantitative_phase_chart_of_oscillation psi z0 r hr (hpsi.mono hsub) ha c hcaxis hc hosc
  have hkappa : ((‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹-c)⁻¹ : ℝ≥0) ≤
      (2*B : ℝ) := by
    rw [NNReal.coe_inv,NNReal.coe_sub hc.le,NNReal.coe_inv,coe_nnnorm]
    rw [← one_div]
    apply (div_le_iff₀ (sub_pos.mpr hcReal)).mpr
    have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*B)
    have he : 2*B*(1/(2*B)) = 1 := by field_simp
    rw [he] at hm
    nlinarith
  have hInvFirst : ∀ y ∈ a.target, ‖fderiv ℝ a.symm y‖ ≤ 2*B :=
    fun y hy => (hfirstInv y hy).trans hkappa
  have hpoint (x) (hx : x ∈ a.source) : fderiv ℝ psi x (0,(1,0)) ≠ 0 := by
    have hxball : x ∈ ball z0 r := by rwa [hs] at hx
    have he := (fderiv ℝ psi x-fderiv ℝ psi z0).le_opNorm (0,(1,0))
    have hv : |fderiv ℝ psi x (0,(1,0))-fderiv ℝ psi z0 (0,(1,0))| ≤ (c:ℝ) := by
      simpa using he.trans (mul_le_mul_of_nonneg_right (hosc x hxball) (norm_nonneg _))
    intro hzero
    rw [hzero,zero_sub,abs_neg] at hv
    exact (not_le.mpr hcaxis) hv
  have hInv : ∀ x ∈ a.source, (fderiv ℝ a x).IsInvertible := by
    intro x hx
    have hxball : x ∈ ball z0 r := by rwa [hs] at hx
    have hd := actual_phase_coordinate_hasFDerivAt psi x
      ((hpsi.contDiffAt (isOpen_ball.mem_nhds (hsub hxball))).differentiableAt (by simp))
    refine ⟨actualPhaseTriangularEquiv (fderiv ℝ psi x) (hpoint x hx),?_⟩
    rw [hfun,hd.fderiv]
    rfl
  have hInvBase : ∀ x ∈ a.source, ‖(fderiv ℝ a x).inverse‖ ≤ 2*B := by
    intro x hx
    have he := actual_inverse_chart_fderiv a hAs hInv (a x) (a.map_source hx)
    rw [a.left_inv hx] at he
    rw [← he]
    exact hInvFirst (a x) (a.map_source hx)
  refine ⟨a,hs,hfun,hAs,hAis,hid,?_,hInvFirst,?_⟩
  · apply (closedBall_subset_closedBall ?_).trans htarget
    rw [NNReal.coe_sub hc.le,NNReal.coe_inv,coe_nnnorm]
    have hm := mul_le_mul_of_nonneg_right hgap (by positivity : 0 ≤ r/2)
    have he : (1/(2*B))*(r/2) = r/(4*B) := by field_simp; ring
    rwa [he] at hm
  · intro j weight Mj hweight hMj hjet
    have hfwd : ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
        weight^i*‖iteratedFDeriv ℝ (i+1) a x‖ ≤ Mj := by
      intro i hi hij x hx
      have hxball : x ∈ ball z0 r := by rwa [hs] at hx
      rw [hfun,actual_phase_coordinate_higher_jet_norm psi x
        (hpsi.contDiffAt (isOpen_ball.mem_nhds (hsub hxball))) i hi]
      exact hjet i hi hij x (hsub hxball)
    exact (actual_inverse_chart_slow_positive_jets a hAs hInv j weight (2*B) Mj hweight
      (by positivity) hMj hInvBase hfwd).2

/-- Original construction-scale specialization of the same chart. -/
theorem actual_exists_uniform_quantitative_phase_chart
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : Ep × (ℝ × Et) → ℝ) (z0 : Ep × (ℝ × Et)) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (haxis : mu ≤ |fderiv ℝ psi z0 (0,(1,0))|)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell * ‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph (Ep × (ℝ × Et)) (Ep × (ℝ × Et)),
      a.source = ball z0 (ell/(4*actualPhaseInverseConstant mu M*(1+M))) ∧
      (a : (Ep × (ℝ × Et)) → (Ep × (ℝ × Et))) = actualPhaseCoordinateMap psi ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2.1) ∧
      closedBall (actualPhaseCoordinateMap psi z0)
        ((ell/(4*actualPhaseInverseConstant mu M*(1+M)))/(4*actualPhaseInverseConstant mu M))
          ⊆ a.target ∧
      (∀ y ∈ a.target, ‖fderiv ℝ a.symm y‖ ≤ 2*actualPhaseInverseConstant mu M) ∧
      (∀ (j : ℕ) (Mj : ℝ), 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          ell^i * ‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          ell^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualInverseChartMajorant (slowInverseMajorant (2*actualPhaseInverseConstant mu M) Mj j) j) := by
  obtain ⟨a,hs,hfun,hAs,hAis,hid,htarget,hfirstInv,hjets⟩ :=
    actual_exists_uniform_quantitative_phase_chart_all_scales mu M hmu hM
      psi z0 ell hell hpsi haxis hfirst hsecond
  exact ⟨a,hs,hfun,hAs,hAis,hid,htarget,hfirstInv,
    fun j Mj hMj hjet => hjets j ell Mj hell hMj hjet⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_phase_chart

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_quantitative_phase_chart_all_scales
