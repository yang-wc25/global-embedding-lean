import Round2.MetricLeftInverse

/-!
# Compact uniform control of the actual tangent left inverse

The constant is selected from the reference immersion before any new map,
parameter ball or probe scale. Exact metric preservation fixes the Gram operator
and the norm of the actual first jet. The conclusion therefore applies uniformly
to all smooth same-metric maps, including the later successive probe stages.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Continuity of the inverse of the actual reference Gram field on each
original chart. Invertibility is derived from the original immersion. -/
theorem continuousOn_probeAtlasGramInverse
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (i : Fin A.count) :
    ContinuousOn (fun x ↦ ((probeAtlasFirstJet A F i x).adjoint.comp
      (probeAtlasFirstJet A F i x)).inverse) (A.chart i).source := by
  have hfirst := continuousOn_probeAtlasFirstJet A hA F hF i
  have hadj := ContinuousLinearMap.adjoint.continuous.comp_continuousOn hfirst
  have hgram := hadj.clm_comp hfirst
  intro x hx
  have hinv := (frame_gram_positive_invertible (probeAtlasFirstJet A F i x)
    (probeAtlasFirstJet_injective A hA F hF i x hx (himm x))).2.2
  have hcinv : ContinuousAt (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      ((probeAtlasFirstJet A F i x).adjoint.comp (probeAtlasFirstJet A F i x)) :=
    (hinv.contDiffAt_map_inverse (n := 1)).continuousAt
  exact hcinv.comp_continuousWithinAt (f := fun y : M ↦
    (probeAtlasFirstJet A F i y).adjoint.comp (probeAtlasFirstJet A F i y)) (hgram x hx)

/-- A single positive constant controls the actual Gram left inverses of every
smooth same-metric perturbation, on every original compact atlas support.
There is no bound or regularity assumption on a normal identification. -/
theorem exists_uniform_sameMetric_tangentLeftInverse_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) →
      ∀ i x, x ∈ A.support i → ‖probeAtlasTangentLeftInverse A G i x‖ ≤ K := by
  have hc (i : Fin A.count) : ContinuousOn
      (fun x ↦ ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖)
      (A.support i) :=
    ((continuousOn_probeAtlasGramInverse A hA F hF himm i).norm.mul
      (continuousOn_probeAtlasFirstJet A hA F hF i).norm).mono (hA.support_subset i)
  choose B hB using fun i ↦ (hcompact i).exists_bound_of_continuousOn (hc i)
  obtain ⟨C, hC⟩ := Finite.exists_le B
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro G hG hmetric i x hx
  calc
    ‖probeAtlasTangentLeftInverse A G i x‖ ≤
        ‖((probeAtlasFirstJet A F i x).adjoint.comp
          (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖ :=
      probeAtlasTangentLeftInverse_norm_le_reference A hA F G hF hG i x
        (hA.support_subset i hx) (hmetric x)
    _ ≤ ‖‖((probeAtlasFirstJet A F i x).adjoint.comp
          (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖‖ :=
      le_abs_self _
    _ ≤ B i := hB i x hx
    _ ≤ |C| + 1 := (hC i).trans ((le_abs_self C).trans (by linarith))

end GlobalEmbedding.Upgrade
