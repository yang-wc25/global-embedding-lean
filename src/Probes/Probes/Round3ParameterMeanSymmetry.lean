import Probes.Round3ParameterPrimaryConstruction

noncomputable section
open GlobalEmbedding.Paper Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]

theorem round3ParameterPrimaryMean_symmetric
    (F : P → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (p : P) (x : M) :
    (round3ParameterPrimaryMean F hF g input length tau p x).IsSymm := by
  constructor
  intro v w
  simp only [round3ParameterPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul]
  simp_rw [real_inner_comm]
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimaryMean_symmetric
