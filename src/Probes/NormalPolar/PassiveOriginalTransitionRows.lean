import NormalPolar.PassiveOriginalTransitionMatrix
import NormalPolar.PassiveOriginalCoordinateRows

/-! The unchanged original transition matrix is exactly the selection of
its two genuine blocks and the two zero mixed blocks. This identifies
whole coordinate functions on the original overlap before any higher
coordinate partial or norm is taken. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

def passiveOriginalMatrixSelect (n d : ℕ) (a : Fin ((n+d)*(n+d))) :
    Option (Fin (n*n) ⊕ Fin (d*d)) :=
  Fin.addCases
    (fun r => Fin.addCases (fun c => some (.inl (finProdFinEquiv (r,c))))
      (fun _ => none) (finProdFinEquiv.symm a).2)
    (fun r => Fin.addCases (fun _ => none)
      (fun c => some (.inr (finProdFinEquiv (r,c)))) (finProdFinEquiv.symm a).2)
    (finProdFinEquiv.symm a).1

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginal_givenTransition_rows
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))
    (hd : IncrementsOriginalDomainConditions seed) (b₀ : Fin seed.parameterCount)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hsChart : s₀ ∈ (seed.parameterChart b₀).source) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count)) :
    EqOn (actualOriginalGivenTransitionDifferentialCoordinates (passiveOriginalData s₀ seed B Q) ik)
      (passiveOriginalSelectTwoRows (passiveOriginalMatrixSelect n d)
        (actualOriginalGivenTransitionDifferentialCoordinates seed ((ik.1.1,b₀),(ik.2.1,b₀)) ∘
          passiveOriginalSourceProjection)
        (passiveOriginalParameterTransitionDifferential B (ik.1.2,ik.2.2) ∘
          passiveOriginalParameterProjection))
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik) := by
  intro y hy
  funext a
  obtain ⟨⟨r,c⟩,rfl⟩ := finProdFinEquiv.surjective a
  simp only [actualOriginalGivenTransitionDifferentialCoordinates,Equiv.symm_apply_apply]
  rw [passiveOriginal_givenTransition_matrix_entry s₀ seed B Q hdP hd b₀ hb₀ hsChart hB hforward ik y hy]
  refine Fin.addCases (fun r₀ => ?_) (fun r₁ => ?_) r
  · refine Fin.addCases (fun c₀ => ?_) (fun c₁ => ?_) c <;>
      simp only [passiveOriginalSelectTwoRows,passiveOriginalMatrixSelect,
        Equiv.symm_apply_apply,Fin.addCases_left,Fin.addCases_right,Function.comp_apply,
        actualOriginalGivenTransitionDifferentialCoordinates]
    have he : (finProdFinEquiv.symm (finProdFinEquiv (r₀,c₀)) : Fin n × Fin n) = (r₀,c₀) :=
      Equiv.symm_apply_apply _ _
    change _ = (fderiv ℝ (actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀))
      (passiveOriginalSourceProjection y)) (Pi.single
        (finProdFinEquiv.symm (finProdFinEquiv (r₀,c₀)) : Fin n × Fin n).2 1)
        (finProdFinEquiv.symm (finProdFinEquiv (r₀,c₀)) : Fin n × Fin n).1
    rw [he]
  · refine Fin.addCases (fun c₀ => ?_) (fun c₁ => ?_) c <;>
      simp only [passiveOriginalSelectTwoRows,passiveOriginalMatrixSelect,
        Equiv.symm_apply_apply,Fin.addCases_left,Fin.addCases_right,Function.comp_apply,
        passiveOriginalParameterTransitionDifferential]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_rows
