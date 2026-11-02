import Probes.ActualFullProbeConnection
import Probes.ActualFullProbeHessianBounds

/-!
# Full first-step covariant Hessian error from actual source and geometry jets

This adds the fixed connection to the proved complete free-plus-homogeneous
Hessian bound. The additional response uses the actual first derivatives of
both reconstruction channels. All constants retain the finite dictionary sum.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

private noncomputable local instance fullBoundBilinearSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance fullBoundBilinearNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fullBoundBilinearNormedSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace


/-- The complete actual homogeneous first-block connection remainder, with
both original channels and all finite source labels, has the required o(sigma)
budget at the original scale choices. -/
theorem actualFullProbe_connection_remainders_bound
    (label : (Fin r × Bool) ↪ Fin p) (δ τ ell : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hphaseSmooth : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (Mg : ℝ) (K Mphase : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hMg : 0 ≤ Mg) (hK : ∀ l, 0 ≤ K l)
    (hAb : ∀ a ≤ 2+order+1, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA F hF c) y‖ ≤ Mg)
    (hBb : ∀ a ≤ 2+order+1, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB F hF c) y‖ ≤ Mg)
    (hGb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) F (c z)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ 2, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue F c) y‖ ≤ Mg)
    (hkb : ∀ l q a, a ≤ 2+order+1 → ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (k l q) y‖ ≤ K l * δ * τ)
    (hphase : ∀ l a, a < 2 → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a+1) (fun z ↦ weight l * phase l z) y‖ ≤ Mphase l)
    (x : D) (hx : x ∈ S) (i : Fin r) (hw : 0 < weight i)
    (K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hamp₀ : ‖amplitude i x‖ ≤ K₀)
    (hamp₁ : ‖fderiv ℝ (amplitude i) x‖ ≤ K₁ / ell)
    (hamp₂ : ‖fderiv ℝ (fderiv ℝ (amplitude i)) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ (phase i) x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ (phase i)) x‖ ≤ P₂ / ell)
    (Γ : D →L[ℝ] D →L[ℝ] D) :
    let Cslow := K₂ / weight i ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / weight i
    let Cfirst := K₁ / weight i ^ 2 + P₁ * K₀ / weight i
    let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l)
    (‖actualProbeCosConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, false)))) x‖ ≤
      (δ / τ) * ((τ / ell) * (Cslow + (1 + τ * ‖Γ‖) * Csum) + τ * Cfirst * ‖Γ‖)) ∧
    (‖actualProbeSinConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, true)))) x‖ ≤
      (δ / τ) * ((τ / ell) * (Cslow + (1 + τ * ‖Γ‖) * Csum) + τ * Cfirst * ‖Γ‖)) := by
  let Cslow := K₂ / weight i ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / weight i
  let Cfirst := K₁ / weight i ^ 2 + P₁ * K₀ / weight i
  let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l)
  let R (q : Fin p) := ∑ l, fderiv ℝ (fderiv ℝ
    (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q))) x
  let L (q : Fin p) := ∑ l, fderiv ℝ
    (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x
  have hH := actualFullProbe_hessian_remainders_bound label δ τ ell weight phase amplitude F hF c
    order k O S hO hSO hphaseSmooth hamplitude hA hB hG hJ hT0 hk Mg K Mphase
    hδ hell hell1 hτ hτell hMg hK hAb hBb hGb hJb hT0b hkb hphase x hx i hw
    K₀ K₁ K₂ P₁ P₂ hK₀ hK₁ hK₂ hP₁ hP₂ hamp₀ hamp₁ hamp₂ hψ₁ hψ₂
  change (‖actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x + R (label (i, false))‖ ≤
    (δ / τ) * (τ / ell) * (Cslow + Csum)) ∧
    (‖actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x + R (label (i, true))‖ ≤
    (δ / τ) * (τ / ell) * (Cslow + Csum)) at hH
  have hrec (l : Fin r) (q : Fin p) := actualRealHomogeneousProbe_weighted_bounds
    (fun y ↦ weight l * phase l y) F hF c 2 order O S hO hSO
    ((hphaseSmooth l).const_smul (weight l)) hA hB hG hJ hT0 (k l q) (hk l q)
    δ ell τ Mg (K l) (Mphase l) hδ hell hell1 hτ hτell hMg (hK l)
    hAb hBb hGb hJb hT0b (hkb l q) (hphase l)
  have hL (q : Fin p) : ‖L q‖ ≤ δ * (τ / ell) * Csum := by
    calc
      _ ≤ ∑ l, ‖fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l q)) x‖ := norm_sum_le _ _
      _ ≤ ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l) * δ * (τ / ell) := by
        apply Finset.sum_le_sum
        intro l _
        exact (actual_wave_value_first_second_scales _ x
          (actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l)) δ τ ell hτ
          (fun n hn ↦ hrec l q n hn x hx)).2.1
      _ = _ := by dsimp [Csum]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
  have hp : DifferentiableAt ℝ (phase i) x :=
    ((hphaseSmooth i).contDiffAt (hO.mem_nhds (hSO hx))).differentiableAt (by simp)
  have ha : DifferentiableAt ℝ (amplitude i) x :=
    ((hamplitude i).contDiffAt (hO.mem_nhds (hSO hx))).differentiableAt (by simp)
  have hDc := norm_fderiv_actualProbeCosColumn_slow_scale x hp ha δ τ ell (weight i)
    K₀ K₁ P₁ hδ hτ hw hτell hK₁ hP₁ hamp₀ hamp₁ hψ₁
  have hDs := norm_fderiv_actualProbeSinColumn_slow_scale x hp ha δ τ ell (weight i)
    K₀ K₁ P₁ hδ hτ hw hτell hK₁ hP₁ hamp₀ hamp₁ hψ₁
  have hgen (Q : D →L[ℝ] D →L[ℝ] V) (T : D →L[ℝ] V)
      (hQ : ‖Q‖ ≤ (δ / τ) * (τ / ell) * (Cslow + Csum))
      (hT : ‖T‖ ≤ δ * (Cfirst + (τ / ell) * Csum)) :
      ‖Q - probeConnectionComposition Γ T‖ ≤
        (δ / τ) * ((τ / ell) * (Cslow + (1 + τ * ‖Γ‖) * Csum) + τ * Cfirst * ‖Γ‖) := by
    calc
      _ ≤ ‖Q‖ + ‖probeConnectionComposition Γ T‖ := norm_sub_le _ _
      _ ≤ (δ / τ) * (τ / ell) * (Cslow + Csum) +
          (δ * (Cfirst + (τ / ell) * Csum)) * ‖Γ‖ :=
        add_le_add hQ ((norm_probeConnectionComposition_apply_le Γ T).trans
          (mul_le_mul_of_nonneg_right hT (norm_nonneg Γ)))
      _ = _ := by field_simp <;> ring
  constructor
  · have he : actualProbeCosConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ
          (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
            (k l (label (i, false)))) x =
        (actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x + R (label (i, false))) -
          probeConnectionComposition Γ (fderiv ℝ
            (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x + L (label (i, false))) := by
      simp only [actualProbeCosConnectionRemainder, probeFixedConnectionHessian, R, L,
        map_add, map_sum, Finset.sum_sub_distrib]
      abel
    rw [he]
    apply hgen _ _ hH.1
    exact (norm_add_le _ _).trans ((add_le_add hDc (hL (label (i, false)))).trans_eq (by dsimp [Cfirst]; ring))
  · have he : actualProbeSinConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ
          (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
            (k l (label (i, true)))) x =
        (actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x + R (label (i, true))) -
          probeConnectionComposition Γ (fderiv ℝ
            (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x + L (label (i, true))) := by
      simp only [actualProbeSinConnectionRemainder, probeFixedConnectionHessian, R, L,
        map_add, map_sum, Finset.sum_sub_distrib]
      abel
    rw [he]
    apply hgen _ _ hH.2
    exact (norm_add_le _ _).trans ((add_le_add hDs (hL (label (i, true)))).trans_eq (by dsimp [Cfirst]; ring))

#print axioms actualFullProbe_connection_remainders_bound
end GlobalEmbedding.Offline
