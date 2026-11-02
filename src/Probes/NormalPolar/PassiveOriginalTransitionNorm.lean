import NormalPolar.PassiveOriginalTransitionRows
import NormalPolar.PassiveOriginalParameterNorm

/-! Full original transition norms for the constructed compact parameter
input. The same original transition matrix, domains, sample sets and
sorted scalar partials are used. Its two true diagonal blocks give the
seed transition cost plus the independently constructed parameter cost;
no norm or output estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
  (hd : IncrementsOriginalDomainConditions seed) (b₀ : Fin seed.parameterCount)
  (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
  (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
  (hs₀ : s₀ ∈ seed.parameterSet)
  (hsChart : s₀ ∈ (seed.parameterChart b₀).source) (hB : IsSmoothBufferedAtlas B)
  (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
    𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))

include hdP hd hb₀ hQ₀ hs₀ hsChart hB hforward

theorem passiveOriginal_givenTransition_Cj_le (j : ℕ) :
    paperAtlasCj j (actualOriginalGivenTransitionDifferentialCoordinates (passiveOriginalData s₀ seed B Q))
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q))
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q)) ≤
    paperAtlasCj j (actualOriginalGivenTransitionDifferentialCoordinates seed)
      (actualOriginalGivenTransitionDomain seed) (actualOriginalGivenTransitionSample seed) +
    paperAtlasCj j (passiveOriginalParameterTransitionDifferential B)
      (passiveOriginalParameterTransitionDomain B) (passiveOriginalParameterTransitionSample B Q) := by
  rw [paperAtlasCj_congr_on j
    (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q))
    (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q))
    (fun _ _ hy => hy.2)
    (passiveOriginal_givenTransition_rows s₀ seed B Q hdP hd b₀ hb₀ hsChart hB hforward)]
  unfold paperAtlasCj
  refine iSup_le fun ik => ?_
  refine (passiveOriginal_selectTwoRows_norm_le j (passiveOriginalMatrixSelect n d) _ _ _ _).trans ?_
  apply add_le_add
  · refine (passiveOriginal_raw_paperCoordinateCj_le j
      (actualOriginalGivenTransitionDifferentialCoordinates seed ((ik.1.1,b₀),(ik.2.1,b₀)))
      (actualOriginalGivenTransitionDomain seed ((ik.1.1,b₀),(ik.2.1,b₀)))
      (actualOriginalGivenTransitionSample seed ((ik.1.1,b₀),(ik.2.1,b₀)))
      (actualOriginalGivenTransitionDomain_open seed _)
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionDomain_open (passiveOriginalData s₀ seed B Q) ik)
      (passiveOriginal_givenTransitionDomain_source s₀ seed B Q b₀ hb₀ hsChart ik)
      (fun _ hy => hy.2)
      (passiveOriginal_givenTransitionSample_source s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hsChart ik)).trans ?_
    exact le_iSup_of_le ((ik.1.1,b₀),(ik.2.1,b₀)) le_rfl
  · refine (passiveOriginal_parameter_paperCoordinateCj_le j
      (passiveOriginalParameterTransitionDifferential B (ik.1.2,ik.2.2))
      (passiveOriginalParameterTransitionDomain B (ik.1.2,ik.2.2))
      (passiveOriginalParameterTransitionSample B Q (ik.1.2,ik.2.2))
      (passiveOriginalParameterTransitionDomain_open B _)
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionDomain_open (passiveOriginalData s₀ seed B Q) ik)
      (passiveOriginal_givenTransitionDomain_parameter s₀ seed B Q ik)
      (fun _ hy => hy.2)
      (passiveOriginal_givenTransitionSample_parameter s₀ seed B Q ik)).trans ?_
    exact le_iSup_of_le (ik.1.2,ik.2.2) le_rfl

/-- All derivative orders and all scales are compared in the unchanged
original cumulative weighted norm. The additional term is exactly the
actual fixed parameter transition profile. -/
theorem passiveOriginal_givenTransition_weighted_le (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell
      (actualOriginalGivenTransitionDifferentialCoordinates (passiveOriginalData s₀ seed B Q))
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q))
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q)) ≤
    paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates seed)
      (actualOriginalGivenTransitionDomain seed) (actualOriginalGivenTransitionSample seed) +
    passiveOriginalParameterTransitionProfile B Q j ell := by
  unfold passiveOriginalParameterTransitionProfile paperAtlasWeighted
  calc
    _ ≤ ∑ a ∈ Finset.range (j+1), ENNReal.ofReal ell ^ a *
      (paperAtlasCj (a+0) (actualOriginalGivenTransitionDifferentialCoordinates seed)
        (actualOriginalGivenTransitionDomain seed) (actualOriginalGivenTransitionSample seed) +
      paperAtlasCj (a+0) (passiveOriginalParameterTransitionDifferential B)
        (passiveOriginalParameterTransitionDomain B) (passiveOriginalParameterTransitionSample B Q)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_right
        (passiveOriginal_givenTransition_Cj_le s₀ seed B Q hdP hd b₀ hb₀ hQ₀ hs₀ hsChart hB hforward (a+0)) _
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_Cj_le
#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_weighted_le
