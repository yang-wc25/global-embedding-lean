import GlobalEmbedding.Paper.SupportedRankLocalSyzygySpan
import GlobalEmbedding.Paper.SupportedRankLiftedSpan

/-!
# The same quadratic family supplies the full lifted legal span

Source: original `prop:supported-rank`, main.tex 1021–1027. This consumes the
already proved local raw/evaluation span and the already proved t-direction
consumer without duplicating either proof. DAG: `supported-rank-lifted-span-product`.
-/

namespace GlobalEmbedding.Paper

open Module

variable {U K : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup K] [Module ℝ K]

/-- The original scalar t-coordinate, on the SAME literal quadratic column. -/
theorem supportedRankLiftedColumn_quadratic_apply
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (z : U) (t : ℝ) (k : K) :
    supportedRankLiftedColumn (supportedRankQuadraticEvaluation Q) z t k =
      (Q k z z • z, t * Q k z z) := by
  simp [supportedRankLiftedColumn, supportedRankQuadraticEvaluation, mul_comm]

/-- The full q+d raw legal span, from the same actual good quadratic data.
The generic lifted theorem's evaluation-span hypothesis is discharged here;
no desired rank or span is a premise. Source: `prop:supported-rank`, 1021–1027. -/
theorem supportedRankLiftedSpan_quadratic_finrank
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ K]
    [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
    (Q : K →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hQ : ∀ k v w, Q k v w = Q k w v)
    (Ω : Set U) (hΩ : IsOpen Ω) (z : U) (hz : z ∈ Ω) (hz0 : z ≠ 0)
    (J : U ≃ₗ[ℝ] Module.Dual ℝ K) (hJ : ∀ v k, J v k = 2 * Q k z v) :
    finrank ℝ U * (finrank ℝ U + 1) / 2 + finrank ℝ U ≤
      finrank ℝ (supportedRankLiftedSpan (supportedRankQuadraticEvaluation Q) Ω) := by
  have heval := supportedRank_local_evaluation_span Q hQ Ω hΩ z hz J hJ
  have hlift := supportedRankLiftedSpan_finrank (supportedRankQuadraticEvaluation Q) Ω heval
  have hraw := supportedRank_local_raw_span_finrank Q hQ Ω hΩ z hz hz0 J hJ
  have hd : finrank ℝ K = finrank ℝ U := by simpa using J.finrank_eq.symm
  change finrank ℝ (supportedRankLocalRawSpan Q Ω) + finrank ℝ K ≤ _ at hlift
  rw [hd] at hlift
  exact (Nat.add_le_add_right hraw _).trans hlift

end GlobalEmbedding.Paper
