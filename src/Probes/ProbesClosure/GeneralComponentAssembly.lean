import ProbesClosure.GeneralFirstModel
import ProbesClosure.GeneralPrescribedJoint
import Main.OriginalProbeThresholds
import ProbesClosure.BackgroundPaired
import ProbesClosure.SecondaryPaired
import ProbesClosure.GeneralInitializedFour

/-!
# Fixed four-response constants for the same arbitrary-cutoff grouped family

The prescribed component and its joint smoothness are manufactured by the
existing original-family constructors. The actual sharp background and
actual signed secondary are converted on the same initialized ball. Their
parameter norms are paid by constants fixed before t, while the background
retains its linear parameter remainder and the secondary retains its small
modulus. This is the concrete component assembly for the later same-map
identity; no finished first-model or final probe record is an input.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {m N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "d" => Fintype.card (Fin r × Bool)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IM" => 𝓘(ℝ,D)

/-- One fixed constant and two nonnegative vanishing moduli for the literal
sum of the actual background, prescribed family, and complete secondary.
The sharp and secondary inputs below are the component outputs supplied by
the same selected initialized state, not final response hypotheses. -/
theorem general_probes_actual_selected_components_first_four
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (waves : Fin r → OpenSupportedLegalWave F0 hF0)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D) (hcompact : ∀ i, IsCompact (Omega i))
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hCover : ∀ x, ∃ i, x ∈ (actualRepairSamplingAtlas A Omega).support i)
    (B : BufferedAtlas P Ep) (sourceCost rho : ℝ) (hrho : 0 < rho)
    (b : Fin B.count) (p0 : P) (hp0 : p0 ∈ B.inner b)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (hSamples : ∀ i x, x ∈ (actualRepairSamplingAtlas A Omega).support i →
      ∃ y ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples (i,b), y.2 = A.chart i x)
    (CB CS : ℝ) (hCB : 0 ≤ CB) (hCS : 0 ≤ CS) :
    let Aout := actualRepairSamplingAtlas A Omega
    let Initialized := jointMixedParameterInitializedAtlas B sourceCost rho hrho
    let amplitude := passiveOriginalReserveAmplitude sourceCost rho
    let ha := passiveOriginalReserveAmplitude_pos sourceCost rho hrho
    let radius := actualRepairParameterRadius (tensorChartFamilyOfAtlas Initialized)
    let label := (round4PairedParameterIndex r).toEmbedding
    ∃ C : ℝ, 0 ≤ C ∧ ∃ etaH etaV : ℝ → ℝ,
      (∀ t, 0 ≤ etaH t) ∧ (∀ t, 0 ≤ etaV t) ∧
      Tendsto etaH (𝓝[>] 0) (𝓝 0) ∧ Tendsto etaV (𝓝[>] 0) (𝓝 0) ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (t : ℝ), 0 < t → t ≤ 1 →
    ∀ (background : (Fin d → ℝ) → M → V)
      (secondary : P × M → V),
      ProbesBackgroundNativeSharp Aout Initialized Samples b (t^((6:ℝ)/5)) CB background →
      actualProbeInitialSecondaryBallBounds A Omega Initialized CS t secondary →
    let G := fun (u : ProbeParameters r) x => scale • F0 x +
      t^(10:ℕ) • background (probeParameterEmbedding label u) x +
      family.centeredPhysicalPairMap scale hscale (t^(10:ℕ)) (t^((6:ℝ)/5))
        442 Initialized amplitude ha b p0 u x +
      secondary (actualRepairParameterMap (tensorChartFamilyOfAtlas Initialized) b p0
        (probeParameterEmbedding label u),x)
    GeneralWaveFirstFourAt F0 hF0 waves Aout weight G (Metric.ball 0 radius)
      radius t C (etaH t) (etaV t) := by
  intro Aout Initialized amplitude ha radius label
  have hAout : IsSmoothBufferedAtlas Aout := actualRepairSamplingAtlas_smooth A hA Omega hTarget
  have hradius : 0 < radius := actualRepairParameterRadius_pos (tensorChartFamilyOfAtlas Initialized)
  have hbuffer := jointMixedParameterInitializedAtlas_buffer B sourceCost rho hrho
  obtain ⟨CP,hCP,etaPH,etaPV,hPHnon,hPVnon,hPHlim,hPVlim,hPrescribed⟩ :=
    generalLegalWave_initialized_physical_four_responses F0 hF0 hImm waves weight hweight
      family A hA Omega hcompact hTarget B sourceCost rho hrho 442
  let CBN := probesBackgroundNormConstant (m+1) N CB radius
  let CSN := probesSecondaryNormConstant (m+1) N CS
  let C := CBN+CP+CSN+CB
  have hCBN : 0 ≤ CBN := probesBackgroundNormConstant_nonneg (m+1) N hCB hradius.le
  have hCSN : 0 ≤ CSN := probesSecondaryNormConstant_nonneg (m+1) N hCS
  refine ⟨C,by dsimp [C]; positivity,
    (fun t => etaPH t+actualProbeSecondaryModulus CS t),
    (fun t => etaPV t+actualProbeSecondaryModulus CS t),
    (fun t => add_nonneg (hPHnon t) (actualProbeSecondaryModulus_nonneg hCS t)),
    (fun t => add_nonneg (hPVnon t) (actualProbeSecondaryModulus_nonneg hCS t)),
    ?_,?_,?_⟩
  · simpa only [zero_add] using hPHlim.add (actualProbeSecondaryModulus_tendsto CS)
  · simpa only [zero_add] using hPVlim.add (actualProbeSecondaryModulus_tendsto CS)
  intro scale hscale t ht ht1 background secondary hSharp hSecondary G
  obtain ⟨hBJ,hBN,hBR⟩ := probes_background_paired_responses
    Aout hAout Initialized Samples b hSamples t CB ht ht1 hCB background hSharp label
  obtain ⟨hSJ,hSV,hSH,hSN⟩ := probes_signed_secondary_paired
    A hA Omega hTarget hCover Initialized CS t secondary hSecondary label b p0 hp0
  have hPJ := family.centeredPhysicalPairMap_chart_joint hImm hweight scale hscale
    (t^(10:ℕ)) (t^((6:ℝ)/5)) 442 Aout hAout Initialized amplitude ha hbuffer b p0 hp0
  have hPN := hPrescribed scale hscale t ht ht1 b p0 hp0
  refine (general_probes_first_four_of_same_components F0 hF0 waves Aout hAout hCover weight
    (Metric.ball 0 radius) Metric.isOpen_ball radius t ht
    (scale • F0) (contMDiff_const_rescale F0 hF0 scale)
    (fun u x => t^(10:ℕ) • background (probeParameterEmbedding label u) x)
    (family.centeredPhysicalPairMap scale hscale (t^(10:ℕ)) (t^((6:ℝ)/5))
      442 Initialized amplitude ha b p0)
    (fun u x => secondary (actualRepairParameterMap (tensorChartFamilyOfAtlas Initialized)
      b p0 (probeParameterEmbedding label u),x))
    hBJ hPJ hSJ CBN CP CSN CB (etaPH t) (etaPV t) (actualProbeSecondaryModulus CS t)
    hCBN hCP hCSN hCB ?_ hPN ?_ (fun u hu _ => hBR u hu) ?_).2
  · intro u hu hur direction
    have hb := hBN u hu direction
    have hc := probes_background_norm_coefficients (m+1) N hCB u hur.le
    exact ⟨hb.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc.1 (pow_nonneg ht.le _)) (norm_nonneg _))),
      hb.2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc.2 (Real.rpow_nonneg ht.le _)) (norm_nonneg _)))⟩
  · intro u hu _ direction
    have hs := hSN u hu direction
    have hc := probes_secondary_norm_coefficients (m+1) N hCS ht.le ht1
    exact ⟨hs.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc.1 (pow_nonneg ht.le _)) (norm_nonneg _))),
      hs.2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc.2 (Real.rpow_nonneg ht.le _)) (norm_nonneg _)))⟩
  · intro u hu _ i x hx direction
    exact ⟨hSV u hu x direction,(hSH u hu i x hx direction).2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.general_probes_actual_selected_components_first_four
