import GlobalEmbedding.Offline.BufferedSmoothingConsumers

/-!
# The same actual smoothing of Euclidean embedding maps

Source: `main.tex` 700–720, maps valued in the genuine Euclidean target.
The operator commutes with a continuous linear equivalence, by actual indicator
identities and Bochner-integral naturality. This identifies the coordinatewise
Pi presentation with the SAME Euclidean-valued map; no sup-norm/Euclidean-norm
isometry is asserted. The final estimate uses the original component norms.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

section Naturality

variable {E F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace E] [TopologicalSpace M]

omit [NormedSpace ℝ E] [MeasurableSpace E] in
/-- Actual coordinate zero extension commutes with a genuine linear equivalence. -/
theorem bufferedCoordinateExtension_equiv (A : BufferedAtlas M E) (e : F ≃L[ℝ] G)
    (u : M → F) (i : Fin A.count) :
    bufferedCoordinateExtension A (e ∘ u) i = e ∘ bufferedCoordinateExtension A u i := by
  funext z
  by_cases hz : z ∈ (A.chart i).target
  · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hz, Function.comp_apply]
  · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hz, Function.comp_apply, map_zero]

/-- Naturality of the actual local integral, including the Bochner convention
outside the buffered region. Invertibility preserves integrability. -/
theorem bufferedLocalSmoothing_equiv (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (e : F ≃L[ℝ] G) (u : M → F) (i : Fin A.count) :
    bufferedLocalSmoothing A mu K ell (e ∘ u) i = e ∘ bufferedLocalSmoothing A mu K ell u i := by
  funext z
  change (∫ y, K y • bufferedCoordinateExtension A (e ∘ u) i (z - ell • y) ∂mu) =
    e (∫ y, K y • bufferedCoordinateExtension A u i (z - ell • y) ∂mu)
  rw [bufferedCoordinateExtension_equiv]
  simpa only [Function.comp_apply, map_smul] using e.integral_comp_comm
    (fun y => K y • bufferedCoordinateExtension A u i (z - ell • y))

/-- The actual global operator commutes with the same linear target equivalence.
This is an equality of the original finite sums and actual convolution integrals. -/
theorem bufferedSmoothing_equiv (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (e : F ≃L[ℝ] G) (u : M → F) :
    bufferedSmoothing A mu K ell chi (e ∘ u) = e ∘ bufferedSmoothing A mu K ell chi u := by
  funext x
  change (∑ i, bufferedSmoothingTerm A mu K ell chi (e ∘ u) i x) =
    e (∑ i, bufferedSmoothingTerm A mu K ell chi u i x)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ (A.chart i).source
  · simp only [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_mem hx,
      Function.comp_apply, bufferedLocalSmoothing_equiv, map_smul]
  · simp only [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_notMem hx,
      smul_zero, map_zero]

end Naturality

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

/-- Literal components of the actual Euclidean map in the original source charts. -/
def bufferedEuclideanCoordinates (A : BufferedAtlas M (Fin d → ℝ))
    (u : M → EuclideanSpace ℝ (Fin q)) :=
  bufferedAtlasCoordinates A (EuclideanSpace.equiv (Fin q) ℝ ∘ u)

omit [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] in
/-- These are exactly the original target-coordinate values, not a changed map. -/
theorem bufferedEuclideanCoordinates_apply (A : BufferedAtlas M (Fin d → ℝ))
    (u : M → EuclideanSpace ℝ (Fin q)) (i : Fin A.count) (x : Fin d → ℝ) (j : Fin q) :
    bufferedEuclideanCoordinates A u i x j = u ((A.chart i).symm x) j := rfl

/-- The actual Euclidean-valued global smoother has the original map base-two
tail bound. Component transport is proved to commute with the SAME smoother,
so this output can be supplied to genuine induced-metric constructions. -/
theorem fixedKernel_buffered_euclidean_map_smoothing_tail (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ A.buffer)
    (m r : ℕ) {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → EuclideanSpace ℝ (Fin q)}
    (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted 2 r t (bufferedEuclideanCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (hNm : paperAtlasWeighted 2 m t (bufferedEuclideanCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 2 r t (bufferedEuclideanCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)).toReal ≤ budget) :
    let K := fixedSmoothingKernel (volume : Measure (Fin d → ℝ)) rho hrho r
    let kappa := normalizedSmoothingBase (volume : Measure (Fin d → ℝ)) rho hrho
    let S := bufferedSmoothing A volume K ell chi u
    let e := bufferedEuclideanCoordinates A (u - S)
    let O := fun i => (A.chart i).target
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ S ∧
      paperAtlasWeighted 2 m tau e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasWeighted 2 m tau e O (bufferedInnerCoordinates A)).toReal ≤
        paperBufferedSmoothingTailConstant volume kappa B T D 2 m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted 2 m t (bufferedEuclideanCoordinates A u)
            O (bufferedSamplingCoordinates A)).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := fixedSmoothingKernel (volume : Measure (Fin d → ℝ)) rho hrho r
  let e : EuclideanSpace ℝ (Fin q) ≃L[ℝ] (Fin q → ℝ) := EuclideanSpace.equiv (Fin q) ℝ
  have huPi : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ (e ∘ u) :=
    e.contDiff.contMDiff.comp hu
  have h := fixedKernel_buffered_map_smoothing_tail A hA rho hrho hbuffer m r htau htaul helt ht1
    chi hchi hchiSupport hpartition huPi B T hB hT D hD hweight htransition hNr hNm budget hbudget
  have hnatural := bufferedSmoothing_equiv A volume K ell chi e u
  have herror : bufferedAtlasCoordinates A ((e ∘ u) - bufferedSmoothing A volume K ell chi (e ∘ u)) =
      bufferedEuclideanCoordinates A (u - bufferedSmoothing A volume K ell chi u) := by
    rw [hnatural]
    funext i z
    exact (e.map_sub _ _).symm
  have hK := fixedSmoothingKernel_spec (volume : Measure (Fin d → ℝ)) rho hrho r
  have hS := bufferedSmoothing_contMDiff A hA volume hK.1 hK.2.1 hK.2.2.1 hbuffer
    (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport hu
  refine ⟨hS, ?_⟩
  rw [← herror]
  exact h.2

end

end GlobalEmbedding.Offline
