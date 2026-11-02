import NormalPolar.OriginalWaveSeedPhysical
import NormalPolar.ActualProbeRescaledLegalWave

/-! The actual solver geometry is jointly smooth throughout a fixed open
interval of positive reference contractions. This keeps the original
adapted chart, phase and normals while selecting future constants uniformly
before the small probe scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => ℝ × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

theorem rescaled_geometry (b : OriginalWaveSeedBuffer d i) (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    let e := b.spatialChart
    let O : Set X := Ioo (1/4 : ℝ) 2 ×ˢ e.target
    let FF := fun c : ℝ => c • F
    let hs := fun c : ℝ => contMDiff_const_rescale F hF c
    ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (FF z.1 ∘ e.symm) z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) (FF z.1) (e.symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (FF z.1) (hs z.1) e.symm z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (FF z.1) e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (FF z.1) (hs z.1) e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (FF z.1) (hs z.1) e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (FF z.1) (hs z.1) e.symm z.2 0 k : V)) O := by
  intro e O FF hs
  let U : Set (ℝ × M) := Ioo (1/4 : ℝ) 2 ×ˢ w.domain
  have hFjoint : ContMDiffOn ((𝓘(ℝ,ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : ℝ × M => FF z.1 z.2) U :=
    (contMDiff_fst.smul (hF.comp contMDiff_snd)).contMDiffOn
  have hpsi : ContMDiffOn ((𝓘(ℝ,ℝ)).prod IM) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => weight * w.phase z.2) U :=
    contMDiffOn_const.mul (w.phase_smooth.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2))
  have hcoords : ContMDiffOn 𝓘(ℝ,X) IM ∞ (fun z : X => e.symm z.2) O :=
    b.spatialChart_inverse_smooth.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2)
  have hmap : MapsTo (fun z : X => (z.1,e.symm z.2)) O U :=
    fun z hz => ⟨hz.1,b.spatialChart_source_original (e.map_target hz.2)⟩
  have hc (z : X) (hz : z ∈ O) : z.1 ≠ 0 := ne_of_gt (by linarith [hz.1.1])
  have hg (z : X) (hz : z ∈ O) : GoodCovector (FF z.1) (hs z.1) (e.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (weight * w.phase (e.symm z.2))).toContinuousLinearMap.comp
        (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm z.2))) := by
    change GoodCovector (z.1 • F) (contMDiff_const_rescale F hF z.1) (e.symm z.2)
      (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm z.2))
    exact (goodCovector_const_rescale_iff F hF z.1 (hc z hz) _ _).mpr
      (b.original_weighted_phase_good hweight z.2 hz.2)
  obtain ⟨_,_,hG,_,hBR,hJ,hT,_,_,hA,hB⟩ :=
    incrementsJointActualGeometry_contDiffOn FF hs (fun _ => e) (fun _ => b.spatialChart_maximal)
      (fun _ x => weight * w.phase x) U O (isOpen_Ioo.prod e.open_target)
      hFjoint hpsi hcoords (fun z hz => hz.2) hmap (isOpen_Ioo.prod w.domain_open)
      (fun z hz => (immersion_const_rescale_iff F hF z.1 (hc z hz) _).mpr (hImm _))
      (fun z hz => b.spatialChart_inverse_phase z.2 hz.2) hg
  exact ⟨hG,hJ,hT,hA,hB,contDiffOn_pi.mpr (fun k => hBR 0 k)⟩

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.rescaled_geometry

