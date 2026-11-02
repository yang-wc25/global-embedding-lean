import Probes.ActualFullProbeFirstStep

/-!
# Quantitative actual Hessian remainder of the combined homogeneous first step

The finite dictionary contributes an explicit sum of the actual two-channel
solver constants. Every solver bound is produced here from native geometry,
phase and source jets; no bound on a desired correction is assumed. Together
with ActualFullProbeFirstStep this bounds the actual mixed Hessian error for
the SAME finite parameter family, uniformly in the base parameter.
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

/-- The actual complete homogeneous first-step Hessian remainder has the
original sigma*tau/ell budget, including every dictionary term and both original
real/imaginary reconstruction channels. -/
theorem actualFullProbe_hessian_remainders_bound
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
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ (phase i)) x‖ ≤ P₂ / ell) :
    let Cslow := K₂ / weight i ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / weight i
    let Csum := ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l)
    (‖actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, false))))) x‖ ≤
      (δ / τ) * (τ / ell) * (Cslow + Csum)) ∧
    (‖actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, true))))) x‖ ≤
      (δ / τ) * (τ / ell) * (Cslow + Csum)) := by
  dsimp only
  have hrec (l : Fin r) (q : Fin p) := actualRealHomogeneousProbe_weighted_bounds
    (fun y ↦ weight l * phase l y) F hF c 2 order O S hO hSO
    ((hphaseSmooth l).const_smul (weight l)) hA hB hG hJ hT0 (k l q) (hk l q)
    δ ell τ Mg (K l) (Mphase l) hδ hell hell1 hτ hτell hMg (hK l)
    hAb hBb hGb hJb hT0b (hkb l q) (hphase l)
  have hH (l : Fin r) (q : Fin p) :
      ‖fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
        F hF c τ order (k l q))) x‖ ≤
      actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l) * (δ / τ) * (τ / ell) :=
    (actual_wave_value_first_second_scales _ x
      (actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l)) δ τ ell hτ
      (fun n hn ↦ hrec l q n hn x hx)).2.2
  have hsum (q : Fin p) :
      ‖∑ l, fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
        F hF c τ order (k l q))) x‖ ≤
      (δ / τ) * (τ / ell) *
        ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l) := by
    calc
      _ ≤ ∑ l, ‖fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l q))) x‖ := norm_sum_le _ _
      _ ≤ ∑ l, actualRealHomogeneousConstant m N 2 order Mg (K l) (Mphase l) *
          (δ / τ) * (τ / ell) := Finset.sum_le_sum (fun l _ ↦ hH l q)
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
  have hp : ContDiffAt ℝ 2 (phase i) x :=
    ((hphaseSmooth i).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp)
  have ha : ContDiffAt ℝ 2 (amplitude i) x :=
    ((hamplitude i).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp)
  have hcos := norm_actualProbeCosRemainder_slow_scale_at x hp ha
    δ τ ell (weight i) K₀ K₁ K₂ P₁ P₂ hδ hτ hw hτell hK₀ hK₁ hK₂ hP₁ hP₂
    hamp₀ hamp₁ hamp₂ hψ₁ hψ₂
  have hsin := norm_actualProbeSinRemainder_slow_scale_at x hp ha
    δ τ ell (weight i) K₀ K₁ K₂ P₁ P₂ hδ hτ hw hτell hK₀ hK₁ hK₂ hP₁ hP₂
    hamp₀ hamp₁ hamp₂ hψ₁ hψ₂
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add hcos (hsum (label (i, false)))).trans_eq (by ring))
  · exact (norm_add_le _ _).trans ((add_le_add hsin (hsum (label (i, true)))).trans_eq (by ring))

#print axioms actualFullProbe_hessian_remainders_bound
end GlobalEmbedding.Offline
