import Probes.Round4PrescribedOriginalMeanCoordinates

/-! A genuine native tensor joint field is transported to the unchanged
source-first original coordinates, including the actual inverse parameter
chart and all ordered spatial tensor entries. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {n d count : ℕ} {M U : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Z" => Fin (n+d) → ℝ
local notation "I" => 𝓘(ℝ,D)

def round4OriginalJointObserverPullback
    (param : Fin count → OpenPartialHomeomorph Ep Ep) (b : Fin count)
    (z : U×Z) : (U×Ep)×D :=
  ((z.1,(param b).symm (incrementsOriginalParameterPoint z.2)),incrementsOriginalSourcePoint z.2)

theorem round4_native_tensor_joint_original_coordinates
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (idx : Fin atlas.count × Fin count)
    (T : U → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (O : Set (U×Z)) (Omega : Set ((U×Ep)×D))
    (hParam : ContDiffOn ℝ ∞ (param idx.2).symm (param idx.2).target)
    (hTarget : ∀ z ∈ O, incrementsOriginalParameterPoint z.2 ∈ (param idx.2).target)
    (hMaps : MapsTo (round4OriginalJointObserverPullback param idx.2) O Omega)
    (hNative : ∀ v w : D, ContDiffOn ℝ ∞ (fun z : (U×Ep)×D =>
      T z.1.1 z.1.2 ((atlas.chart idx.1).symm z.2)
        (mfderiv I I (atlas.chart idx.1).symm z.2 ((tangentSpaceCastModel I z.2).symm v))
        (mfderiv I I (atlas.chart idx.1).symm z.2 ((tangentSpaceCastModel I z.2).symm w))) Omega) :
    ContDiffOn ℝ ∞ (fun z : U×Z =>
      incrementsOriginalTensorCoordinates atlas param (T z.1) idx z.2) O := by
  have hparamPoint : ContDiff ℝ ∞ (incrementsOriginalParameterPoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.contDiff.fst
  have hsourcePoint : ContDiff ℝ ∞ (incrementsOriginalSourcePoint (n := n) (d := d)) :=
    (parameterTensorModelEquiv n d).symm.contDiff.snd
  have hq : ContDiffOn ℝ ∞ (round4OriginalJointObserverPullback (U := U) param idx.2) O :=
    (contDiffOn_fst.prodMk
      (hParam.comp (hparamPoint.comp contDiff_snd).contDiffOn hTarget)).prodMk
      (hsourcePoint.comp contDiff_snd).contDiffOn
  apply contDiffOn_pi.2
  intro k
  exact (hNative (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)
    (EuclideanSpace.single (finProdFinEquiv.symm k).2 1)).comp hq hMaps

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_native_tensor_joint_original_coordinates
