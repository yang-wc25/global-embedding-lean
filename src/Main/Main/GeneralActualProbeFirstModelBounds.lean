import Main.GeneralNativeProbeDomainModelData

/-!
# The remaining quantitative contract for the actual first probe state

This record refers only to the actual preliminary map G.  It contains no
repaired map, repair tail, metric equality, polar reserve, normal isometry,
or identified second-form estimate.  The same-run construction proves those
later facts.  Producing these bounds for the complete first state, including
background and every secondary correction, remains an upstream obligation.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

structure GeneralActualProbeFirstModelBounds
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (A : BufferedAtlas M E) {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    (G : ℝ → ProbeParameters r → M → V) (radius threshold : ℝ) where
  weight : Fin r → ℝ
  weight_pos : ∀ l, 0 < weight l
  distinct_on_overlap : ∀ l k, l ≠ k →
    (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  etaH : ℝ → ℝ
  etaV : ℝ → ℝ
  etaH_nonneg : ∀ t, 0 ≤ etaH t
  etaV_nonneg : ∀ t, 0 ≤ etaV t
  etaH_tendsto : Tendsto etaH (𝓝[>] 0) (𝓝 0)
  etaV_tendsto : Tendsto etaV (𝓝[>] 0) (𝓝 0)
  closeness : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 2 (G t u - F₀) ≤ ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5))
  spatial_C3 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 3 (G t u) ≤ ENNReal.ofReal constant
  parameter_C1 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ G t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ (10 : ℕ) * ‖d‖)
  parameter_C2 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 2 (fun x ↦ fderiv ℝ (fun v ↦ G t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5) * ‖d‖)
  hessian_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b i x, x ∈ A.support i →
      ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (G t v ∘ (A.chart i).symm)) (A.chart i x))
          u (Pi.single (l, b) 1) -
        (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) •
          phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
            ((waves l).value ∘ (A.chart i).symm) (A.chart i x)‖ ≤
        t ^ ((44 : ℝ) / 5) * (etaH t + constant * ‖u‖)
  value_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b x,
      ‖fderiv ℝ (fun v ↦ G t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤
        t ^ ((56 : ℝ) / 5) * (etaV t + constant * ‖u‖)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralActualProbeFirstModelBounds
