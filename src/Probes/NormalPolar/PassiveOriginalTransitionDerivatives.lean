import NormalPolar.PassiveOriginalTransitionBinding
import Probes.ActualOriginalTransitionProfileJets

/-! Exact derivatives of the literal original transition blocks. These
are derivatives of the one explicitly constructed native chart transition,
proved from its global function identities and original chart regularity.
They are not prescribed derivative or norm identities. -/

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

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (hdP : IncrementsOriginalDomainConditions (passiveOriginalData s₀ seed B Q))

include hdP

theorem passiveOriginal_givenTransition_derivative_source
    (hd : IncrementsOriginalDomainConditions seed) (b₀ : Fin seed.parameterCount)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hsChart : s₀ ∈ (seed.parameterChart b₀).source)
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count))
    (y : Fin (n+d) → ℝ)
    (hy : y ∈ actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik) :
    (passiveOriginalSourceProjection (n := n) (d := d)).comp
      (fderiv ℝ (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2) y) =
    (fderiv ℝ (actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀))
      (passiveOriginalSourceProjection y)).comp passiveOriginalSourceProjection := by
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  let F := actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2
  let G := actualOriginalGivenTransition seed (ik.1.1,b₀) (ik.2.1,b₀)
  have hF : DifferentiableAt ℝ F y :=
    ((actualOriginalGivenTransition_contDiffOn (passiveOriginalData s₀ seed B Q) hdP ik).contDiffAt
      ((actualOriginalGivenTransitionDomain_open (passiveOriginalData s₀ seed B Q) ik).mem_nhds hy)).differentiableAt (by simp)
  have hmem := passiveOriginal_givenTransitionDomain_source s₀ seed B Q b₀ hb₀ hsChart ik hy
  have hG : DifferentiableAt ℝ G (L y) :=
    ((actualOriginalGivenTransition_contDiffOn seed hd ((ik.1.1,b₀),(ik.2.1,b₀))).contDiffAt
      ((actualOriginalGivenTransitionDomain_open seed _).mem_nhds hmem)).differentiableAt (by simp)
  have heq : L ∘ F = G ∘ L := funext (passiveOriginal_givenTransition_source s₀ seed B Q b₀ ik.1 ik.2)
  calc
    _ = fderiv ℝ (L ∘ F) y := (L.hasFDerivAt.comp y hF.hasFDerivAt).fderiv.symm
    _ = fderiv ℝ (G ∘ L) y := congrArg (fun f => fderiv ℝ f y) heq
    _ = _ := (hG.hasFDerivAt.comp y L.hasFDerivAt).fderiv

theorem passiveOriginal_givenTransition_derivative_parameter
    (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count))
    (y : Fin (n+d) → ℝ)
    (hy : y ∈ actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik) :
    (passiveOriginalParameterProjection (n := n) (d := d)).comp
      (fderiv ℝ (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2) y) =
    (fderiv ℝ (passiveOriginalParameterTransition B (ik.1.2,ik.2.2))
      (passiveOriginalParameterProjection y)).comp passiveOriginalParameterProjection := by
  let L := passiveOriginalParameterProjection (n := n) (d := d)
  let F := actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) ik.1 ik.2
  let G := passiveOriginalParameterTransition B (ik.1.2,ik.2.2)
  have hF : DifferentiableAt ℝ F y :=
    ((actualOriginalGivenTransition_contDiffOn (passiveOriginalData s₀ seed B Q) hdP ik).contDiffAt
      ((actualOriginalGivenTransitionDomain_open (passiveOriginalData s₀ seed B Q) ik).mem_nhds hy)).differentiableAt (by simp)
  have hmem := passiveOriginal_givenTransitionDomain_parameter s₀ seed B Q ik hy
  have hG : DifferentiableAt ℝ G (L y) :=
    ((passiveOriginalParameterTransition_smooth B hB hforward (ik.1.2,ik.2.2)).contDiffAt
      ((passiveOriginalParameterTransitionDomain_open B _).mem_nhds hmem)).differentiableAt (by simp)
  have heq : L ∘ F = G ∘ L := funext (passiveOriginal_givenTransition_parameter s₀ seed B Q ik.1 ik.2)
  calc
    _ = fderiv ℝ (L ∘ F) y := (L.hasFDerivAt.comp y hF.hasFDerivAt).fderiv.symm
    _ = fderiv ℝ (G ∘ L) y := congrArg (fun f => fderiv ℝ f y) heq
    _ = _ := (hG.hasFDerivAt.comp y L.hasFDerivAt).fderiv

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_derivative_source
#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_derivative_parameter
