import NormalPolar.OriginalWaveSeedSpatialChart
import GlobalEmbedding.Paper.IncrementsJointActualGeometry
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-! The actual solver geometry of an arbitrary original legal wave.
The finite adapted chart is constructed, not postulated. Original immersion
and the original Good phase produce smoothness of the literal first/Hessian
fields and the actual A, B, G, J, T and second-form-row fields. No coefficient
smoothness, Gram inverse or reconstructed-wave estimate is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

theorem exists_outer (b : OriginalWaveSeedBuffer d i) :
    ∃ b' : OriginalWaveSeedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget := by
  obtain ⟨L,hL,hBL,hLT⟩ := exists_compact_between b.compact (d.chart i).open_target b.contained
  exact ⟨⟨L,hL,hLT,b.contains_support.trans (interior_subset.trans hBL)⟩,hBL⟩

/-- All original geometric coefficients for this constructed adapted chart. -/
theorem original_geometry (b : OriginalWaveSeedBuffer d i) (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    let e := b.spatialChart
    let O : Set X := univ ×ˢ e.target
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F ∘ e.symm) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (fderiv ℝ (F ∘ e.symm)) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F ∘ e.symm) z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) F (e.symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ F hF e.symm z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue F e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA F hF e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB F hF e.symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm F hF e.symm z.2 0 k : V)) O := by
  intro e O
  let W : Set (Z × M) := univ ×ˢ w.domain
  have hFjoint : ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : Z × M => F z.2) W := (hF.comp contMDiff_snd).contMDiffOn
  have hpsi : ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,ℝ) ∞
      (fun z : Z × M => weight * w.phase z.2) W :=
    contMDiffOn_const.mul (w.phase_smooth.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2))
  have hcoords : ContMDiffOn 𝓘(ℝ,X) IM ∞ (fun z : X => e.symm z.2) O :=
    b.spatialChart_inverse_smooth.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2)
  have hmap : MapsTo (fun z : X => (z.1,e.symm z.2)) O W := by
    intro z hz
    exact ⟨mem_univ _,b.spatialChart_source_original (e.map_target hz.2)⟩
  have hgood (z : X) (hz : z ∈ O) : GoodCovector F hF (e.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (weight * w.phase (e.symm z.2))).toContinuousLinearMap.comp
        (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm z.2))) := by
    have hdom := (hmap hz).2
    have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt
      (by simp)
    have he : mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm z.2) =
        weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase (e.symm z.2) :=
      (hd.hasMFDerivAt.const_smul weight).mfderiv
    change GoodCovector F hF (e.symm z.2)
      (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm z.2))
    rw [he]
    exact (good_covector_smul_iff F hF (e.symm z.2) _ weight hweight.ne').mpr
      ((w.legal (e.symm z.2) hdom).1)
  obtain ⟨hFirst,hSecond,hG,hNormal,hBR,hJ,hT,hAr,hBr,hA,hB⟩ :=
    incrementsJointActualGeometry_contDiffOn (fun _ : Z => F) (fun _ => hF)
      (fun _ => e) (fun _ => b.spatialChart_maximal) (fun _ x => weight * w.phase x)
      W O (isOpen_univ.prod e.open_target) hFjoint hpsi hcoords (fun z hz => hz.2)
      hmap (isOpen_univ.prod w.domain_open) (fun z _ => hImm (e.symm z.2))
      (fun z hz => b.spatialChart_inverse_phase z.2 hz.2) hgood
  exact ⟨hFirst,hSecond,hG,hJ,hT,hA,hB,contDiffOn_pi.mpr (fun k => hBR 0 k)⟩

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.original_geometry
