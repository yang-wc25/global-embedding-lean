import UpgradeContinuation.CompactReferenceSetup
import Upgrade.CompactFixedAtlasPhase
import Probes.Round4ActualTemplateField
import Initialization.Phase.SelectorJetComparison

/-!
# Native reference reserves from the actual original immersion

The phase operator consumed by the native local factory is identified with
the already verified fixed-atlas projected second form.  The compact reserve
theorem then applies on the actual compact coordinate norm domains.  This
manufactures the quantitative inputs from the qualitative original phase
regularity and immersion conditions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.Upgrade
open scoped ContDiff Topology TensorProduct Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

/-- The native template factory and the existing upgrade geometry use the
same true normal Hessian, with the original symmetric-square normalization. -/
theorem nativeReferencePhase_eq_projected
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (i : Fin A.count) (p : Z) (y : D) (hy : y ∈ (A.chart i).target) :
    round4ActualPhaseOperatorInChart (fun _ : Z => F) (fun _ => A.chart i) (p,y) =
      probeAtlasProjectedSecondForm A F i ((A.chart i).symm y) := by
  have hx := (A.chart i).map_target hy
  have hnormal := normalSpace_eq_probeAtlasFirstJet_range A hA F hF i
    ((A.chart i).symm y) hx
  have hprojection : (probeAtlasFirstJet A F i ((A.chart i).symm y)).rangeᗮ.starProjection =
      (normalSpace (I := IM) F ((A.chart i).symm y)).starProjection := by
    congr 1
    exact hnormal.symm
  unfold round4ActualPhaseOperatorInChart actualNormalHessianInChart
  change actualHessianLift
    (((ContinuousLinearMap.compL ℝ D V V)
      (normalSpace (I := IM) F ((A.chart i).symm y)).starProjection).comp
        (fderiv ℝ (fderiv ℝ (F ∘ (A.chart i).symm)) y)) = _
  rw [GlobalEmbedding.Initialization.actualHessianLift_postcomp]
  unfold probeAtlasProjectedSecondForm probeAtlasSecondJet coordinateHessianJet
  rw [hprojection, (A.chart i).right_inv hy]

/-- Uniform positive first-jet and phase reserves are extracted from the
same original map on the actual compact coordinate sampling domains. -/
theorem exists_nativeReference_coordinate_reserves
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D)
    (hcompact : ∀ i, IsCompact (Omega i))
    (htarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hdim : 2 ≤ m+1)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF) :
    ∃ lower margin : ℝ, 0 < lower ∧ 0 < margin ∧
      ∀ i p y, y ∈ Omega i →
        (∀ v : D, lower*‖v‖^2 ≤ ‖fderiv ℝ (F ∘ (A.chart i).symm) y v‖^2) ∧
        margin ≤ bestPhaseSupremum
          (round4ActualPhaseOperatorInChart (fun _ : Z => F) (fun _ => A.chart i) (p,y)) := by
  let K : BufferedAtlas M D :=
    { A with support := fun i => (A.chart i).symm '' Omega i }
  have hK : IsSmoothBufferedAtlas K := {
    chart_mem := hA.chart_mem
    support_subset := by
      intro i x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact (A.chart i).map_target (htarget i hy) }
  have hKcompact (i : Fin K.count) : IsCompact (K.support i) :=
    (hcompact i).image_of_continuousOn ((A.chart i).continuousOn_symm.mono (htarget i))
  obtain ⟨lower,B,margin,hlower,hB,hmargin,hres⟩ :=
    exists_fixedAtlas_actual_reference_reserves K hK hKcompact hdim F hF himm hphase
  refine ⟨lower,margin,hlower,hmargin,?_⟩
  intro i p y hy
  have hyT := htarget i hy
  have h := hres i ((A.chart i).symm y) ⟨y,hy,rfl⟩
  constructor
  · simpa only [probeAtlasFirstJet, K, (A.chart i).right_inv hyT] using h.1
  · rw [nativeReferencePhase_eq_projected A hA F hF i p y hyT]
    exact h.2.2

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.nativeReferencePhase_eq_projected
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.exists_nativeReference_coordinate_reserves
