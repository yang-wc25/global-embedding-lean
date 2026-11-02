import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import GlobalEmbedding.External.SphereEversion.Global.OneJetSec
import Mathlib.Analysis.InnerProductSpace.PiL2
import GlobalEmbedding.Paper.FramedPartialImmersionRelation
import GlobalEmbedding.Paper.OpenAmpleMapExistence

/-!
# Smooth zero-valued jets from actual smooth tangent coframes

Source: `lem:planar`, first proof paragraph: the dual coframe defines a formal derivative.
This module supplies the native Hom-bundle to native one-jet smoothness bridge.
-/

open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth tangent-to-trivial-bundle homomorphism yields a smooth genuine zero-valued jet. -/
theorem contMDiff_zeroJet_of_smoothHom
    (B : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)) :
    ContMDiff I ((I.prod 𝓘(ℝ, F)).prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x : M ↦ OneJetBundle.mk x (0 : F)
        ((NormedSpace.fromTangentSpace (0 : F)).symm.toContinuousLinearMap.comp (B x))) := by
  intro x
  have hb := (contMDiffAt_hom_bundle (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := F) (E₂ := fun _ : M ↦ F) (IB := I) (IM := I) (n := (∞ : WithTop ℕ∞))
    (fun y : M ↦ Bundle.TotalSpace.mk' (E →L[ℝ] F) y (B y))).mp (B.contMDiff x)
  apply contMDiffAt_id.oneJetBundle_mk contMDiffAt_const
  convert hb.2 using 1
  ext y v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    NormedSpace.fromTangentSpace]
  rfl

/-- The genuine section of the source one-jet projection with value zero and derivative B. -/
noncomputable def smoothHom_zeroJet
    (B : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)) :
    OneJetSec I M 𝓘(ℝ, F) F where
  bs := fun _ ↦ 0
  ϕ x := (NormedSpace.fromTangentSpace (0 : F)).symm.toContinuousLinearMap.comp (B x)
  contMDiff' := contMDiff_zeroJet_of_smoothHom B

/-- Standard coordinate inclusion of R^b into R^(b+1), with one extra zero coordinate. -/
noncomputable def framedPartial_coordinateInclusion (b : ℕ) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin (b + 1)) :=
  (EuclideanSpace.equiv (Fin (b + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin (b + 1) ↦
      Fin.cases (0 : EuclideanSpace ℝ (Fin b) →L[ℝ] ℝ)
        (fun i ↦ EuclideanSpace.proj (𝕜 := ℝ) i) j)

/-- The coordinate inclusion is injective, including when b=0. -/
theorem framedPartial_coordinateInclusion_injective (b : ℕ) :
    Function.Injective (framedPartial_coordinateInclusion b) := by
  intro u v huv
  ext i
  have hi := congrArg (fun w : EuclideanSpace ℝ (Fin (b + 1)) ↦ w i.succ) huv
  simpa [framedPartial_coordinateInclusion] using hi

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposing an actual smooth coframe by a fixed linear map gives a smooth zero jet. -/
theorem contMDiff_zeroJet_postcompose_smoothHom
    (B : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F))
    (C : F →L[ℝ] G) :
    ContMDiff I ((I.prod 𝓘(ℝ, G)).prod 𝓘(ℝ, E →L[ℝ] G)) ∞
      (fun x : M ↦ OneJetBundle.mk x (0 : G)
        ((NormedSpace.fromTangentSpace (0 : G)).symm.toContinuousLinearMap.comp
          (C.comp (B x)))) := by
  let C' : TangentSpace 𝓘(ℝ, F) (0 : F) →L[ℝ] TangentSpace 𝓘(ℝ, G) (0 : G) :=
    (NormedSpace.fromTangentSpace (0 : G)).symm.toContinuousLinearMap.comp
      (C.comp (NormedSpace.fromTangentSpace (0 : F)).toContinuousLinearMap)
  have hc : ContMDiff I ((𝓘(ℝ, F).prod 𝓘(ℝ, G)).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun _ : M ↦ OneJetBundle.mk (0 : F) (0 : G) C') := contMDiff_const
  convert hc.oneJet_comp 𝓘(ℝ, F) (fun _ : M ↦ (0 : F))
    (contMDiff_zeroJet_of_smoothHom B) using 1
  funext x
  apply Bundle.TotalSpace.ext rfl
  apply heq_of_eq
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The actual formal solution supplied by a true smooth dual coframe. The coframe existence
is a separate geometric theorem; this construction does not assume a desired FormalSol. -/
noncomputable def framedPartial_formal_of_coframe {b : ℕ}
    (V : FramedDistribution I (M := M) b)
    (B : ContMDiffSection I (E →L[ℝ] EuclideanSpace ℝ (Fin b)) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b)))
    (hB : ∀ x i, B x (V.frame i x) = EuclideanSpace.single i 1) :
    FormalSol (framedPartialImmersionRelation (F := EuclideanSpace ℝ (Fin (b + 1))) V) where
  bs := fun _ ↦ 0
  ϕ x := (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (b + 1)))).symm.toContinuousLinearMap.comp ((framedPartial_coordinateInclusion b).comp (B x))
  contMDiff' := contMDiff_zeroJet_postcompose_smoothHom B (framedPartial_coordinateInclusion b)
  is_sol' x := by
    apply (framedPartial_injective_iff V x _).mpr
    change LinearIndependent ℝ (fun i : Fin b ↦
      (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (b + 1)))).symm
        (framedPartial_coordinateInclusion b (B x (V.frame i x))))
    have hbase : LinearIndependent ℝ
        (fun i : Fin b ↦ EuclideanSpace.single i (1 : ℝ)) :=
      EuclideanSpace.orthonormal_single.linearIndependent
    have hinc := hbase.map_injOn (framedPartial_coordinateInclusion b).toLinearMap
      (fun u _ v _ huv ↦ framedPartial_coordinateInclusion_injective b huv)
    have hout := hinc.map_injOn
      (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (b + 1)))).symm.toLinearMap
      (fun u _ v _ huv ↦
        (NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin (b + 1)))).symm.injective huv)
    simpa only [Function.comp_apply, hB] using! hout

/-- The genuine partial immersion obtained from a genuine global smooth coframe by the
accepted maps h-principle. The coframe existence theorem removes this intermediate input. -/
theorem framedPartial_exists_of_smoothCoframe
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {b : ℕ} (V : FramedDistribution I (M := M) b)
    (B : ContMDiffSection I (E →L[ℝ] EuclideanSpace ℝ (Fin b)) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b)))
    (hB : ∀ x i, B x (V.frame i x) = EuclideanSpace.single i 1) :
    ∃ f : M → EuclideanSpace ℝ (Fin (b + 1)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) ∞ f ∧
      ∀ x, Function.Injective (fun v : FramedDistribution.fiber I V x ↦
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) f x v.1) := by
  have hr : b < Module.finrank ℝ (EuclideanSpace ℝ (Fin (b + 1))) := by simp
  obtain ⟨f, hf, hsol⟩ := openAmpleMap_exists_smooth_solution
    (framedPartialImmersionRelation (F := EuclideanSpace ℝ (Fin (b + 1))) V)
    (framedPartialImmersionRelation_open V) (framedPartialImmersionRelation_ample V hr)
    (framedPartial_formal_of_coframe V B hB)
  exact ⟨f, hf, hsol⟩

end GlobalEmbedding.Paper
