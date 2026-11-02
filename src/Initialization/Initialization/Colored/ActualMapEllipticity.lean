import Initialization.Colored.ActualNativeMetric
import Initialization.Assembly.ParameterThresholds

/-!
# Uniform positive ellipticity of the same actual colored map

The original target metric supplies its positive ellipticity reserves. The
actual C⁰ metric error then transfers them to γ(H_(K,T)) for all sufficiently
large real K and T/K. Boundedness of the actual error range is proved before
using its real supremum, so no totalized unbounded-supremum value is used.
-/

noncomputable section
open Set Function Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

section GramNorm

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem actualMetricOperator_norm (H : E → V) (y : E) :
    ‖actualMetricOperator H y‖ = ‖fderiv ℝ H y‖ ^ 2 := by
  simp only [actualMetricOperator, actualGramOperator,
    ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

end GramNorm

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The actual Gram of the same global H has positive lower and upper bounds
throughout every full rescaled chart target. All constants and both real
parameter thresholds are chosen before K,T; no geometric budget is assumed. -/
theorem exists_metricInitializationMap_ellipticity
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ
      (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1) :
    ∃ lower upper K₀ R₀ : ℝ, 0 < lower ∧ 0 < upper ∧ 1 ≤ K₀ ∧ 1 ≤ R₀ ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        K₀ ≤ K → R₀ * K ≤ T →
        ∀ (Q : ChartCutoffFamily G T) (p : Fin Q.count)
          (y : EuclideanSpace ℝ (Fin n)),
          y ∈ ((Q.boundedAtlas (hK.trans hKT)).chart p).target →
          ∀ v : EuclideanSpace ℝ (Fin n),
            lower * ‖v‖ ^ 2 ≤ inner ℝ
              (actualMetricOperator
                (metricInitializationMap G g f S K T hK ∘
                  ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y v) v ∧
            inner ℝ
              (actualMetricOperator
                (metricInitializationMap G g f S K T hK ∘
                  ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y v) v ≤
              upper * ‖v‖ ^ 2 := by
  obtain ⟨targetLower, targetUpper, hLower, hUpper, htarget⟩ :=
    exists_scaledTargetMetric_ellipticity G g f
  obtain ⟨metricB, _hmetricB, hmetricRef⟩ := exists_scaledTargetMetric_derivative_bounds G g f
  obtain ⟨R, _A, hR, _hA, href⟩ := exists_actualSelectedSource_jet_bounds G g f S hS
  obtain ⟨C, hC, herror⟩ := exists_metricInitializationMap_cj_bounds G g f S hS hGram
  obtain ⟨K₀, R₀, hK₀, hR₀, hsmall⟩ := initialization_error_scale_eventually_small
    (C 0) (targetLower / 2) (hC 0).le (half_pos hLower)
  refine ⟨targetLower / 2, targetUpper + targetLower / 2, K₀, R₀,
    half_pos hLower, add_pos hUpper (half_pos hLower), hK₀, hR₀, ?_⟩
  intro K T hK hKT hKK hTT Q p y hy v
  let H := metricInitializationMap G g f S K T hK ∘
    ((Q.boundedAtlas (hK.trans hKT)).chart p).symm
  let target := scaledTargetMetricOperator G g f Q p
  let err := fun z ↦ actualMetricOperator H z - target z
  let O := ((Q.boundedAtlas (hK.trans hKT)).chart p).target
  have hderiv (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ O) : ‖fderiv ℝ H z‖ ≤ R 1 := by
    have heq : H = actualSelectedCoordinate G g f S (preparedCutoffsAt G K hK)
        Q (hK.trans hKT) p :=
      metricInitializationMap_pullback_eq_actualSelectedCoordinate G g f S hK Q (hK.trans hKT) p
    rw [heq]
    simpa only [norm_iteratedFDeriv_one] using
      ((href K T hK hKT (preparedCutoffsAt G K hK) Q p 1).1 z hz).1
  have hbounded : ∀ k ≤ 0,
      BddAbove (Set.range fun z : O ↦ ‖iteratedFDeriv ℝ k err z‖) := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    refine ⟨(R 1)^2 + metricB 0, ?_⟩
    rintro _ ⟨z, rfl⟩
    change ‖iteratedFDeriv ℝ 0 err (z : EuclideanSpace ℝ (Fin n))‖ ≤ _
    rw [norm_iteratedFDeriv_zero]
    have hmap : ‖actualMetricOperator H z‖ ≤ (R 1)^2 := by
      rw [actualMetricOperator_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hderiv z z.property) 2
    have hmetric : ‖target z‖ ≤ metricB 0 := by
      simpa only [norm_iteratedFDeriv_zero] using
        (hmetricRef T (hK.trans hKT) Q p 0 z z.property).2
    exact (norm_sub_le _ _).trans (add_le_add hmap hmetric)
  have hpoint : ‖err y‖ ≤ C 0 * (K⁻¹ + K/T) := by
    have hp := (finiteCjNorm_specification 0 err O hbounded).2.1 0 le_rfl y hy
    rw [norm_iteratedFDeriv_zero] at hp
    exact hp.trans (herror K T hK hKT Q p 0)
  have hsmall' : ‖err y‖ ≤ targetLower / 2 :=
    hpoint.trans ((hsmall K T hKK hTT).2.2.2.le)
  have hquad : |inner ℝ (actualMetricOperator H y v) v - inner ℝ (target y v) v| ≤
      (targetLower / 2) * ‖v‖^2 := by
    calc
      _ = |inner ℝ (err y v) v| := by
        simp only [err, sub_apply, inner_sub_left]
      _ ≤ ‖err y v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖err y‖ * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((err y).le_opNorm v) (norm_nonneg _)
      _ = ‖err y‖ * ‖v‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall' (sq_nonneg _)
  have hlohi := htarget T (hK.trans hKT) Q p y hy v
  have habs := abs_le.mp hquad
  constructor <;> nlinarith [hlohi.1, hlohi.2, habs.1, habs.2]

end GlobalEmbedding.Initialization
