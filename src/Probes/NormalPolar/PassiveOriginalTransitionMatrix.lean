import NormalPolar.PassiveOriginalTransitionDerivatives

/-! Every coefficient of the actual original transition derivative is
exactly its seed source block, its constructed parameter block, or zero.
The original ordered coordinate matrix is retained, including both mixed
blocks and zero dimensions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
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

theorem passiveOriginal_givenTransition_matrix_entry
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
    (hd : IncrementsOriginalDomainConditions seed) (b₀ : Fin seed.parameterCount)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hsChart : s₀ ∈ (seed.parameterChart b₀).source) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count))
    (y : Fin (n+d) → ℝ)
    (hy : y ∈ actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik)
    (r c : Fin (n+d)) :
    fderiv ℝ (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2) y
      (Pi.single c 1) r =
    Fin.addCases
      (fun r₀ => Fin.addCases
        (fun c₀ => fderiv ℝ (actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀))
          (passiveOriginalSourceProjection y) (Pi.single c₀ 1) r₀)
        (fun _ => 0) c)
      (fun r₁ => Fin.addCases (fun _ => 0)
        (fun c₁ => fderiv ℝ (passiveOriginalParameterTransition B (ik.1.2,ik.2.2))
          (passiveOriginalParameterProjection y) (Pi.single c₁ 1) r₁) c) r := by
  have hs := passiveOriginal_givenTransition_derivative_source s₀ seed B Q hdP hd b₀ hb₀ hsChart ik y hy
  have hp := passiveOriginal_givenTransition_derivative_parameter s₀ seed B Q hdP hB hforward ik y hy
  refine Fin.addCases (fun r₀ => ?_) (fun r₁ => ?_) r
  · refine Fin.addCases (fun c₀ => ?_) (fun c₁ => ?_) c
    · have h := congrArg (fun A : (Fin (n+d) → ℝ) →L[ℝ] (Fin n → ℝ) =>
        A (Pi.single (Fin.castAdd d c₀) 1) r₀) hs
      change (fderiv ℝ (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2) y)
        (Pi.single (Fin.castAdd d c₀) 1) (Fin.castAdd d r₀) =
        (fderiv ℝ (actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀))
        (passiveOriginalSourceProjection y))
        (passiveOriginalSourceProjection (n := n) (d := d) (Pi.single (Fin.castAdd d c₀) 1)) r₀ at h
      simpa only [Fin.addCases_left,passiveOriginalSourceProjection_single_source] using h
    · have h := congrArg (fun A : (Fin (n+d) → ℝ) →L[ℝ] (Fin n → ℝ) =>
        A (Pi.single (Fin.natAdd n c₁) 1) r₀) hs
      change (fderiv ℝ (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2) y)
        (Pi.single (Fin.natAdd n c₁) 1) (Fin.castAdd d r₀) =
        (fderiv ℝ (actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀))
        (passiveOriginalSourceProjection y))
        (passiveOriginalSourceProjection (n := n) (d := d) (Pi.single (Fin.natAdd n c₁) 1)) r₀ at h
      simpa only [Fin.addCases_left,Fin.addCases_right,
        passiveOriginalSourceProjection_single_parameter (Fin.natAdd n c₁) (by simp),
        map_zero,Pi.zero_apply] using h
  · refine Fin.addCases (fun c₀ => ?_) (fun c₁ => ?_) c
    · have h := congrArg (fun A : (Fin (n+d) → ℝ) →L[ℝ] (Fin d → ℝ) =>
        A (Pi.single (Fin.castAdd d c₀) 1) r₁) hp
      simpa only [Fin.addCases_left,Fin.addCases_right,ContinuousLinearMap.comp_apply,
        passiveOriginalParameterProjection_apply,passiveOriginalParameterProjection_single_source,
        map_zero,Pi.zero_apply] using h
    · have h := congrArg (fun A : (Fin (n+d) → ℝ) →L[ℝ] (Fin d → ℝ) =>
        A (Pi.single (Fin.natAdd n c₁) 1) r₁) hp
      simpa only [Fin.addCases_right,ContinuousLinearMap.comp_apply,
        passiveOriginalParameterProjection_apply,passiveOriginalParameterProjection_single_parameter] using h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_matrix_entry
