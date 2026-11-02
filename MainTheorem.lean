import Main.OriginalUpgradeMain

/-!
# Small-image isometric embedding of a closed parallelizable manifold

Let M be a closed smooth parallelizable n-manifold, n ≥ 3. Every smooth
positive definite metric on M is induced by a smooth phase-regular embedding
into the radius-r ball in ℝ^(n(n+1)/2+1), for every r > 0.

The complete statement is written below. The proof applies the constructed
main endpoint; its implementation is in `Main.OriginalUpgradeMain`.
See `docs/PROOF_GUIDE.md` for a reading guide.
-/

noncomputable section
open Set Manifold Bundle Topology GlobalEmbedding.Paper
open scoped ContDiff ENNReal

namespace GlobalEmbedding
universe uM

/-- The closed parallelizable small-image isometric embedding theorem.
All output properties concern the same map F. -/
theorem small_image_isometric_embedding
    {n : ℕ} {M : Type uM}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (hn : 3 ≤ n)
    (hpar : IsParallelizable (M := M) 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) n)
    (metric0 : ContMDiffRiemannianMetric 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _))
    (r : ℝ) (hr : 0 < r) :
    ∃ F : M → EuclideanSpace ℝ (Fin (n*(n+1)/2+1)),
    ∃ hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (n*(n+1)/2+1))) ∞ F,
      inducedMetric (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) F =
        (fun x => (metric0.inner x).toLinearMap₁₂) ∧
      (∀ x, Function.Injective
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
          𝓘(ℝ,EuclideanSpace ℝ (Fin (n*(n+1)/2+1))) F x)) ∧
      PhaseRegular (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) F hF ∧
      IsEmbedding F ∧ Set.range F ⊆ Metric.ball 0 r := by
  exact GlobalEmbedding.Main.endpoint_main hn hpar metric0 r hr

end GlobalEmbedding

#print axioms GlobalEmbedding.small_image_isometric_embedding
