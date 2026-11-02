import Upgrade.CompactProbeAtlas
import Upgrade.ProtectionSupported

/-!
# Literal two-stage original C² budgets used in the finite upgrade chain

These are specializations of the already proved finite telescoping budget.
The source and target coordinate norms are unchanged. The arithmetic rank
dictionary uses the normal space of the actual current immersion.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem probeAtlasC2_two_stage_budget
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F₀ F₁ F₂ : M → V)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF₁ : ContMDiff IM 𝓘(ℝ, V) ∞ F₁)
    (hF₂ : ContMDiff IM 𝓘(ℝ, V) ∞ F₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : probeAtlasCj A 2 (F₁ - F₀) ≤ ENNReal.ofReal a)
    (h₂ : probeAtlasCj A 2 (F₂ - F₁) ≤ ENNReal.ofReal b) :
    probeAtlasCj A 2 (F₂ - F₀) ≤ ENNReal.ofReal (a + b) := by
  let F : ℕ → M → V := fun k ↦ if k = 0 then F₀ else if k = 1 then F₁ else F₂
  let c : ℕ → ℝ := fun k ↦ if k = 0 then a else b
  have hsmooth : ∀ k ≤ 2, ContMDiff IM 𝓘(ℝ, V) ∞ (F k) := by
    intro k hk
    interval_cases k <;> simpa [F] using (by assumption)
  have hnonneg : ∀ k < 2, 0 ≤ c k := by
    intro k hk
    interval_cases k <;> simp [c, ha, hb]
  have hstep : ∀ k < 2, probeAtlasCj A 2 (F (k + 1) - F k) ≤ ENNReal.ofReal (c k) := by
    intro k hk
    interval_cases k
    · simpa [F, c] using h₁
    · simpa [F, c] using h₂
  have h := finite_probeAtlas_prefix_budget A hA 2 2 F hsmooth c hnonneg hstep 2 le_rfl
  simpa [F, c, Finset.sum_range_succ] using h

theorem probeAtlasC2_self_le_zero
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) :
    probeAtlasCj A 2 (F - F) ≤ 0 := by
  have h := finite_probeAtlas_prefix_budget A hA 2 0 (fun _ ↦ F)
    (fun _ _ ↦ hF) (fun _ ↦ (0 : ℝ)) (by simp) (by simp) 0 le_rfl
  simpa using h

theorem upgrade_normal_codimension (hn : 1 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1) : N - n = n * (n - 1) / 2 + 1 := by
  have hprod : n * (n + 1) = n * (n - 1) + 2 * n := by
    calc
      n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
      _ = n * (n - 1) + 2 * n := by ring
  omega

theorem actual_fullRank_of_rank_gt_q
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (x : M) (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hn : 1 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : n * (n - 1) / 2 < finrank ℝ (trueSecondForm F hF x).range) :
    Function.Surjective (trueSecondForm F hF x) := by
  apply (trueSecondForm_surjective_iff_finrank_ge F hF x himm).mpr
  rw [finrank_euclideanSpace_fin, upgrade_normal_codimension hn hN]
  exact hrank

end GlobalEmbedding.Upgrade
