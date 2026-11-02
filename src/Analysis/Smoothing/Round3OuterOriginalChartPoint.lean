import Smoothing.ParameterRound2OriginalInputs
import Probes.ActualIncrementOriginalCoordinateJets

/-! The literal source-first original chart point is jointly smooth on its
unchanged differentiation domain. This is the coordinate map used by the
actual fixed-reference cover, including its parameter component.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Y" => Fin (n+d) → ℝ

theorem round3_original_jointPoint_contMDiffOn
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (i : Fin A.count × Fin c) :
    ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) ∞
      (incrementsOriginalJointPoint A B i) (incrementsOriginalDifferentiation A B i) := by
  let e := (B i.2).prod (A.chart i.1)
  have he : e ∈ maximalAtlas ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) ∞ (P × M) :=
    mem_maximalAtlas_prod (hB i.2) (hA.chart_mem i.1)
  have hi := contMDiffOn_symm_of_mem_maximalAtlas he
  have hmap : MapsTo (parameterTensorModelEquiv n d).symm
      (incrementsOriginalDifferentiation A B i) e.target := by
    intro y hy
    exact ⟨hy.2,hy.1⟩
  exact hi.comp (parameterTensorModelEquiv n d).symm.contDiff.contMDiff.contMDiffOn hmap

#print axioms round3_original_jointPoint_contMDiffOn
end GlobalEmbedding.Continuation
