import NormalPolar.PassiveOriginalCoordinates

/-! The actual enlarged source norm pieces and each original parameter norm
piece map to the seed evaluation domain. All source and primary support sets
are retained exactly; this is the missing sampling fact needed to use the
constant-one native coordinate budget comparison. -/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)

theorem passiveOriginal_jointPoint
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection y) =
      (s₀,(incrementsOriginalJointPoint seed.atlas B.chart i y).2) :=
  Prod.ext (Subsingleton.elim _ _) rfl

theorem passiveOriginal_differentiation_projection
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (i : Fin seed.atlas.count × Fin B.count) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (incrementsOriginalDifferentiation seed.atlas B.chart i)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart (i.1,b₀)) := by
  intro y hy
  refine ⟨hy.1,?_⟩
  have hp : incrementsOriginalParameterPoint (n := n) (d := 0) (passiveOriginalSourceProjection y) =
      (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  exact hp.symm ▸ hb₀

theorem passiveOriginal_evaluation_projection
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
    (hs₀ : s₀ ∈ seed.parameterSet) (i : Fin seed.atlas.count × Fin B.count) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ i)
      (incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
        seed.parameterNormDomain seed.parameterSet (i.1,b₀)) := by
  intro y hy
  have hp : incrementsOriginalParameterPoint (n := n) (d := 0) (passiveOriginalSourceProjection y) =
      (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  refine ⟨passiveOriginal_differentiation_projection seed B b₀ hb₀ i hy.1,hy.2.1,hp.symm ▸ hQ₀,?_⟩
  rw [passiveOriginal_jointPoint s₀ seed B b₀]
  exact hs₀

theorem passiveOriginal_primaryDifferentiation_projection
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (l : Fin seed.primaryCount) (i : Fin seed.atlas.count × Fin B.count) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l i)
      (incrementsOriginalPrimaryDifferentiation seed l (i.1,b₀)) := by
  intro y hy
  refine ⟨passiveOriginal_differentiation_projection seed B b₀ hb₀ i hy.1,?_⟩
  change incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection y) ∈ seed.primaryDomain l
  rw [passiveOriginal_jointPoint s₀ seed B b₀]
  exact hy.2

theorem passiveOriginal_primaryEvaluation_projection
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
    (hs₀ : s₀ ∈ seed.parameterSet) (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (incrementsOriginalPrimaryEvaluation (passiveOriginalData s₀ seed B Q) l i)
      (incrementsOriginalPrimaryEvaluation seed l (i.1,b₀)) := by
  intro y hy
  refine ⟨passiveOriginal_evaluation_projection s₀ seed B Q b₀ hb₀ hQ₀ hs₀ i hy.1,?_⟩
  change incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection y) ∈ seed.primaryDomain l
  rw [passiveOriginal_jointPoint s₀ seed B b₀]
  exact hy.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_evaluation_projection
#print axioms GlobalEmbedding.Continuation.passiveOriginal_primaryEvaluation_projection
