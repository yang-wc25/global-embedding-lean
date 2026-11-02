import NormalPolar.JointSecondarySignedBuffers
import GlobalEmbedding.Paper.IncrementsJointActualGeometry
import Probes.ActualIncrementFreeNormalKernel
import NormalPolar.ActualProbeRescaledLegalWave

/-! The same signed-phase charts and partition work throughout a fixed positive
contraction interval. All actual solver fields are jointly smooth in the
contraction and spatial coordinates, before any probe scale is selected. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "X" => ℝ × D

variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}

namespace JointSecondarySignedBuffer

theorem actual_phase_rescaled_geometry
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (hsource : e.source ⊆ O)
    (hinverse : ∀ y ∈ e.target, phase (e.symm y) = y 0)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hO : IsOpen O) (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hgood : ∀ x ∈ O, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    let FF := fun c : ℝ => c • F
    let hs := fun c : ℝ => contMDiff_const_rescale F hF c
    ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (FF z.1 ∘ e.symm) z.2)) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) ∧
    ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) (FF z.1) (e.symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (FF z.1) (hs z.1) e.symm z.2)) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (FF z.1) e.symm z.2) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (FF z.1) (hs z.1) e.symm z.2) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (FF z.1) (hs z.1) e.symm z.2) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) ∧
    ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (FF z.1) (hs z.1) e.symm z.2 0 k : V)) (Ioo (1/4 : ℝ) 2 ×ˢ e.target) := by
  intro FF hs
  let W : Set (ℝ × M) := Ioo (1/4 : ℝ) 2 ×ˢ O
  let U : Set X := Ioo (1/4 : ℝ) 2 ×ˢ e.target
  have hFjoint : ContMDiffOn ((𝓘(ℝ,ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : ℝ × M => FF z.1 z.2) W :=
    (contMDiff_fst.smul (hF.comp contMDiff_snd)).contMDiffOn
  have hpsi : ContMDiffOn ((𝓘(ℝ,ℝ)).prod IM) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => phase z.2) W :=
    hphase.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2)
  have hcoords : ContMDiffOn 𝓘(ℝ,X) IM ∞ (fun z : X => e.symm z.2) U :=
    (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2)
  have hmap : MapsTo (fun z : X => (z.1,e.symm z.2)) U W :=
    fun z hz => ⟨hz.1,hsource (e.map_target hz.2)⟩
  have hc (z : X) (hz : z ∈ U) : z.1 ≠ 0 := ne_of_gt (by linarith [hz.1.1])
  have hg (z : X) (hz : z ∈ U) : GoodCovector (FF z.1) (hs z.1) (e.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (phase (e.symm z.2))).toContinuousLinearMap.comp
        (mfderiv IM 𝓘(ℝ,ℝ) phase (e.symm z.2))) := by
    change GoodCovector (z.1 • F) (contMDiff_const_rescale F hF z.1) (e.symm z.2)
      (mfderiv IM 𝓘(ℝ,ℝ) phase (e.symm z.2))
    exact (goodCovector_const_rescale_iff F hF z.1 (hc z hz) _ _).mpr
      (hgood _ (hsource (e.map_target hz.2)))
  obtain ⟨_,_,hG,_,hBR,hJ,hT,_,_,hA,hB⟩ :=
    incrementsJointActualGeometry_contDiffOn FF hs (fun _ => e) (fun _ => he)
      (fun _ => phase) W U (isOpen_Ioo.prod e.open_target)
      hFjoint hpsi hcoords (fun z hz => hz.2) hmap (isOpen_Ioo.prod hO)
      (fun z hz => (immersion_const_rescale_iff F hF z.1 (hc z hz) _).mpr (hImm _))
      (fun z hz => hinverse z.2 hz.2) hg
  exact ⟨hG,hJ,hT,hA,hB,contDiffOn_pi.mpr (fun k => hBR 0 k)⟩

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.actual_phase_rescaled_geometry
