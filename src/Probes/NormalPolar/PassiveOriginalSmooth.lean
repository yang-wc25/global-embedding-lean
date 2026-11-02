import NormalPolar.PassiveOriginalCoordinates

/-! Joint smoothness of the actual original passive data.  It is derived
from the seed original smooth-input record and an actual covering seed chart;
no smoothness of a completed first increment is assumed. -/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginalData_smooth
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (hs : IncrementsOriginalSmoothInputs seed) (hs₀ : s₀ ∈ seed.parameterOpen)
    (b₀ : Fin seed.parameterCount)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) :
    IncrementsOriginalSmoothInputs (passiveOriginalData s₀ seed B Q) := by
  let κ : P × M → S × M := fun z => (s₀,z.2)
  have hκ : ContMDiff
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin n)))
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) ∞ κ :=
    contMDiff_const.prodMk contMDiff_snd
  refine {
    F_joint := hs.F_joint.comp hκ.contMDiffOn (fun _ _ => ⟨hs₀,mem_univ _⟩)
    H_coordinates := ?_
    phase_joint := fun l => (hs.phase_joint l).comp hκ.contMDiffOn
      (fun z hz => ⟨hz.1,hs₀,mem_univ _⟩)
    cutoff_joint := fun l => (hs.cutoff_joint l).comp hκ.contMDiffOn
      (fun z hz => ⟨hz.1,hs₀,mem_univ _⟩)
    normal_joint := fun l => (hs.normal_joint l).comp hκ.contMDiffOn
      (fun z hz => ⟨hz.1,hs₀,mem_univ _⟩) }
  intro i
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  have hmap : MapsTo L
      (incrementsOriginalDifferentiation seed.atlas B.chart i ∩
        (incrementsOriginalJointPoint seed.atlas B.chart i) ⁻¹'
          incrementsOriginalParameterRegion (passiveOriginalData s₀ seed B Q))
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart (i.1,b₀) ∩
        (incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)) ⁻¹'
          incrementsOriginalParameterRegion seed) := by
    intro y hy
    have hp : incrementsOriginalParameterPoint (n := n) (d := 0) (L y) = (0 : EuclideanSpace ℝ (Fin 0)) :=
      Subsingleton.elim _ _
    have hs' : (incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀) (L y)).1 = s₀ :=
      Subsingleton.elim _ _
    refine ⟨⟨?_,hp.symm ▸ hb₀⟩,?_⟩
    · exact hy.1.1
    · change (incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀) (L y)).1
          ∈ seed.parameterOpen ∧ _
      exact ⟨hs'.symm ▸ hs₀,mem_univ _⟩
  have h := (hs.H_coordinates (i.1,b₀)).comp L.contDiff.contDiffOn hmap
  apply h.congr
  intro y hy
  exact passiveOriginal_tensorCoordinates s₀ seed B b₀ seed.H i y

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalData_smooth
