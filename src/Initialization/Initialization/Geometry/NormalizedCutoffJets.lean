import Initialization.Geometry.RawCutoffJets
import Initialization.Geometry.CenteredRescaling

/-!
# Actual uniform normalized cutoff jets

The actual square sum is bounded using the proved support-graph multiplicity,
and its actual reciprocal square root is bounded using the existing verified
normalization theorem. No denominator, overlap, transition or derivative bound
is left as a new hypothesis. The output controls the same literal normalized
cutoffs used by the actual colored map.
-/

open Set Metric Filter Manifold IsManifold Topology Function
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- Internally produced A_j K^j bounds for every actual normalized cutoff in
every fixed parent core. The sequence precedes K, all net choices and indices. -/
theorem exists_prepared_normalizedCutoff_derivative_bounds (G : PreparedCharts M n) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ K : ℝ, 1 ≤ K → ∀ F : ChartCutoffFamily G K,
        ∀ p i j y, y ∈ ball (G.center p) (2 * G.radius p) →
          ‖iteratedFDeriv ℝ j (F.cutoff i ∘ (G.chart p).symm) y‖ ≤ A j * K ^ j := by
  obtain ⟨B, hB, hraw⟩ := exists_prepared_rawCutoff_derivative_bounds G
  obtain ⟨D, hD⟩ := exists_uniform_rawCutoff_multiplicity G
  obtain ⟨C, hC, hsum⟩ := exists_squareCutoffSum_bounds_of_multiplicity
    (E := EuclideanSpace ℝ (Fin n)) (X := M) B hB D
  obtain ⟨A, hA, hnormalize⟩ := exists_squareNormalizedCutoff_derivative_bounds
    (E := EuclideanSpace ℝ (Fin n)) B C hB hC
  refine ⟨A, hA, ?_⟩
  intro K hK F p i j y hy
  let O := ball (G.center p) (2 * G.radius p)
  let b : Fin F.count → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun v ↦ F.rawCutoff v ∘ (G.chart p).symm
  have hO : IsOpen O := isOpen_ball
  have hOt : O ⊆ (G.chart p).target := by
    intro z hz
    exact G.buffered p ((closedBall_subset_closedBall (by linarith [G.radius_pos p]))
      (ball_subset_closedBall hz))
  have hb (v : Fin F.count) : ContDiffOn ℝ ∞ (b v) O :=
    (((F.rawCutoff_smooth hK v).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth p))).contDiffOn).mono hOt
  have hpos (z : EuclideanSpace ℝ (Fin n)) (_hz : z ∈ O) : 1 ≤ squareCutoffSum b z :=
    F.rawCutoff_squareSum_ge_one hK ((G.chart p).symm z)
  have hbound (v : Fin F.count) (l : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ O) :
      ‖iteratedFDeriv ℝ l (b v) z‖ ≤ B l * K ^ l :=
    hraw K hK F p v l z (ball_subset_closedBall hz)
  have hsumbound (l : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ O) :
      ‖iteratedFDeriv ℝ l (squareCutoffSum b) z‖ ≤ C l * K ^ l :=
    hsum (Fin F.count) K (zero_le_one.trans hK) F.rawCutoff (G.chart p).symm O
      hO hb z hz ((G.chart p).symm.continuousAt (hOt hz)) (hD K hK F _)
      (fun v _ l ↦ hbound v l z hz) l
  have heq : F.cutoff i ∘ (G.chart p).symm = squareNormalizedCutoff b i := by
    rw [F.cutoff_eq_normalized_raw]
    rfl
  rw [heq]
  exact hnormalize (Fin F.count) K hK b O hO hb hpos hsumbound i
    (hbound i) j y hy

/-- The same actual cutoffs in any genuine scale-T atlas have the full
(K/T)^j gain. K,T are real, with T≥K≥1, and the constant sequence was chosen
before both. In particular every differentiated cutoff carries K/T. -/
theorem exists_rescaled_normalizedCutoff_derivative_bounds (G : PreparedCharts M n) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (K T : ℝ), ∀ hK : 1 ≤ K, ∀ hKT : K ≤ T,
      ∀ (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T),
        ∀ p i j y,
          Q.center p + T⁻¹ • y ∈
            ball (G.center (Q.parent p)) (2 * G.radius (Q.parent p)) →
          ‖iteratedFDeriv ℝ j
            (F.cutoff i ∘ ((Q.scaledAtlas (hK.trans hKT)).chart p).symm) y‖ ≤
            A j * (K / T) ^ j := by
  obtain ⟨A, hA, hbound⟩ := exists_prepared_normalizedCutoff_derivative_bounds G
  refine ⟨A, hA, ?_⟩
  intro K T hK hKT F Q p i j y hy
  have hTpos : 0 < T := zero_lt_one.trans_le (hK.trans hKT)
  change ‖iteratedFDeriv ℝ j
    (F.cutoff i ∘ (rescaledChart (G.chart (Q.parent p)) (Q.center p) T hTpos.ne').symm) y‖ ≤ _
  have heq :
      (F.cutoff i ∘ (rescaledChart (G.chart (Q.parent p)) (Q.center p) T hTpos.ne').symm) =
      (fun z ↦ (F.cutoff i ∘ (G.chart (Q.parent p)).symm) (Q.center p + T⁻¹ • z)) := by
    funext z
    simp only [Function.comp_apply, rescaledChart_symm_apply, add_comm]
  rw [heq, iteratedFDeriv_centered_rescaling _ _ hTpos.ne', norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
  calc
    (T⁻¹) ^ j * ‖iteratedFDeriv ℝ j (F.cutoff i ∘ (G.chart (Q.parent p)).symm)
        (Q.center p + T⁻¹ • y)‖ ≤ (T⁻¹) ^ j * (A j * K ^ j) :=
      mul_le_mul_of_nonneg_left (hbound K hK F (Q.parent p) i j _ hy) (by positivity)
    _ = A j * (K / T) ^ j := by rw [div_eq_mul_inv, mul_pow]; ring

end GlobalEmbedding.Initialization
