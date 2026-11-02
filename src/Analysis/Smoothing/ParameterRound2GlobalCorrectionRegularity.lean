import Smoothing.ParameterRound2GlobalCorrectionSupport
import Probes.ActualJointHomogeneousParameter

/-! Joint smoothness of the SAME local and globally observed corrections,
derived from the actual source, canonical geometry, actual chart and original
combined support. No numerical profile or output regularity is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_globalLocalCorrection_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hsrc : ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target) :
    ContDiffOn ℝ ∞ (parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β)
      (g.chart ν β).target := by
  let U := incrementsGlobalPrimaryFiniteU F hF g input length tau ν β
  let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
    if realChannel then incrementsModeRealPart else incrementsModeImagPart
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) (g.chart ν β).target :=
    actual_joint_mode_sum_contDiffOn F hF (g.inverse ν β)
      (incrementsGlobalPrimarySource F hF g input tau ν β) tau length
      (g.chart ν β).target (g.chart ν β).open_target hA hB hsrc
  have hu := ch.contDiff.comp_contDiffOn hU
  have hd := (incrementsJointSpatialJets_bridge _ (g.chart ν β).target (g.chart ν β).open_target hu).2.1
  have ht : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseTensor (F z.1)
      (g.inverse ν β z.1) (ch ∘ U z.1) z.2) (g.chart ν β).target := by
    exact ((hT.clm_apply hu).add (contDiffOn_const.clm_apply hd)).congr
      (fun z _ => incrementsModeTransverseTensor_split (F z.1) (g.inverse ν β z.1) (ch ∘ U z.1) z.2)
  exact (hG.clm_apply hu).add (hJ.clm_apply ht)

theorem parameterRound2_globalCorrection_observation_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hsupport : incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (kappa : Y → Ep × M) (Omega U : Set Y) (hOmega : IsOpen Omega)
    (hkappa : ContinuousOn kappa Omega) (hmapW : MapsTo kappa Omega W)
    (hU : IsOpen U)
    (hOU : Omega ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ U)
    (hsource : MapsTo kappa U (g.chart ν β).source)
    (hphi : ContDiffOn ℝ ∞ (fun z => g.chart ν β (kappa z)) U)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hsrc : ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target) :
    ContDiffOn ℝ ∞
      (parameterRound2_globalCorrection F hF g input length tau realChannel ν β ∘ kappa) Omega := by
  let R := parameterRound2_globalCorrection F hF g input length tau realChannel ν β
  let Rloc := parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β
  let K := incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)
  have hlocal := parameterRound2_globalLocalCorrection_contDiffOn F hF g input length tau
    realChannel ν β hA hB hG hJ hT hsrc
  have hcomp : ContDiffOn ℝ ∞ (R ∘ kappa) U := by
    apply (hlocal.comp hphi (fun z hz => (g.chart ν β).map_source (hsource hz))).congr
    intro z hz
    exact parameterRound2_globalCorrection_eq_on_source F hF g input length tau realChannel ν β
      hinverse (kappa z) (hsource hz)
  have hs := parameterRound2_globalCorrection_relative_support F hF g input length tau realChannel ν β
    W hW hsupport hinverse
  intro z hz
  by_cases hK : kappa z ∈ K
  · exact (hcomp.contDiffAt (hU.mem_nhds (hOU ⟨hz,hK⟩))).contDiffWithinAt
  · have hzero := parameterRound2_relative_observation_zero_germ R W K hW hs kappa z
      (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmapW hz) hK
    exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt

#print axioms parameterRound2_globalLocalCorrection_contDiffOn
#print axioms parameterRound2_globalCorrection_observation_contDiffOn
end GlobalEmbedding.Continuation
