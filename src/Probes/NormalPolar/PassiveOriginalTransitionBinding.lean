import NormalPolar.PassiveOriginalSamples
import NormalPolar.PassiveOriginalParameterTransitions
import Probes.ActualOriginalGivenProfile

/-! Literal block identities for the original given transition of the
constructed native input. Its source block is the same seed transition;
its parameter block is exactly the actual globally smooth parameter
transition whose fixed costs were constructed. The original overlap and
sample domains map to the corresponding true domains of both blocks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]

def passiveOriginalParameterProjection : (Fin (n+d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd n i))

@[simp] theorem passiveOriginalParameterProjection_apply (y : Fin (n+d) → ℝ) (i : Fin d) :
    passiveOriginalParameterProjection (n := n) y i = y (Fin.natAdd n i) := rfl

theorem passiveOriginalParameterProjection_single_parameter (i : Fin d) :
    passiveOriginalParameterProjection (n := n) (Pi.single (Fin.natAdd n i) 1) =
      Pi.single i 1 := by
  ext j
  simp only [passiveOriginalParameterProjection_apply,Pi.single_apply]
  simp

theorem passiveOriginalParameterProjection_single_source (i : Fin n) :
    passiveOriginalParameterProjection (d := d) (Pi.single (Fin.castAdd d i) 1) = 0 := by
  ext j
  have hne : Fin.castAdd d i ≠ Fin.natAdd n j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  simp only [passiveOriginalParameterProjection_apply,Pi.single_apply,Pi.zero_apply]
  simp [hne,Ne.symm hne]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)

theorem passiveOriginal_givenTransition_source
    (i k : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    passiveOriginalSourceProjection
      (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) i k y) =
    actualOriginalGivenTransition seed (i.1,b₀) (k.1,b₀) (passiveOriginalSourceProjection y) := by
  ext r
  change parameterTensorModelEquiv n d _ (Fin.castAdd d r) =
    parameterTensorModelEquiv n 0 _ (Fin.castAdd 0 r)
  simp only [parameterTensorModelEquiv,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,sourceFirstCoordinates_apply_spatial]
  rfl

theorem passiveOriginal_givenTransition_parameter
    (i k : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    passiveOriginalParameterProjection
      (actualOriginalGivenTransition (passiveOriginalData s₀ seed B Q) i k y) =
    passiveOriginalParameterTransition B (i.2,k.2) (passiveOriginalParameterProjection y) := by
  ext r
  change parameterTensorModelEquiv n d _ (Fin.natAdd n r) = _
  simp only [parameterTensorModelEquiv,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,sourceFirstCoordinates_apply_parameter]
  rfl

theorem passiveOriginal_givenTransitionDomain_source
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hs₀ : s₀ ∈ (seed.parameterChart b₀).source)
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count)) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionDomain seed ((ik.1.1,b₀),(ik.2.1,b₀))) := by
  intro y hy
  refine ⟨passiveOriginal_differentiation_projection seed B b₀ hb₀ ik.1 hy.1,?_⟩
  change incrementsOriginalJointPoint seed.atlas seed.parameterChart (ik.1.1,b₀)
      (passiveOriginalSourceProjection y) ∈
    (seed.parameterChart b₀).source ×ˢ (seed.atlas.chart ik.2.1).source
  rw [passiveOriginal_jointPoint s₀ seed B b₀ ik.1 y]
  exact ⟨hs₀,hy.2.2⟩

theorem passiveOriginal_givenTransitionSample_source
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
    (hs₀ : s₀ ∈ seed.parameterSet) (hsChart : s₀ ∈ (seed.parameterChart b₀).source)
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count)) :
    MapsTo (passiveOriginalSourceProjection (d := d))
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q) ik)
      (actualOriginalGivenTransitionSample seed ((ik.1.1,b₀),(ik.2.1,b₀))) := by
  intro y hy
  exact ⟨passiveOriginal_evaluation_projection s₀ seed B Q b₀ hb₀ hQ₀ hs₀ ik.1 hy.1,
    passiveOriginal_givenTransitionDomain_source s₀ seed B Q b₀ hb₀ hsChart ik hy.2⟩

theorem passiveOriginal_givenTransitionDomain_parameter
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count)) :
    MapsTo (passiveOriginalParameterProjection (n := n))
      (actualOriginalGivenTransitionDomain (passiveOriginalData s₀ seed B Q) ik)
      (passiveOriginalParameterTransitionDomain B (ik.1.2,ik.2.2)) := by
  intro y hy
  exact hy.1.2

theorem passiveOriginal_givenTransitionSample_parameter
    (ik : (Fin seed.atlas.count × Fin B.count) × (Fin seed.atlas.count × Fin B.count)) :
    MapsTo (passiveOriginalParameterProjection (n := n))
      (actualOriginalGivenTransitionSample (passiveOriginalData s₀ seed B Q) ik)
      (passiveOriginalParameterTransitionSample B Q (ik.1.2,ik.2.2)) := by
  intro y hy
  exact hy.1.2.2.1

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_source
#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransition_parameter
#print axioms GlobalEmbedding.Continuation.passiveOriginal_givenTransitionSample_source
