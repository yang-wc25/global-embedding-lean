import NormalPolar.OriginalWaveSeedGroupedIdentity
import NormalPolar.PassiveGroupedPrescribed
import NormalPolar.OriginalWaveSeedParameterBall
import NormalPolar.GlobalWaveResponsePaired

/-! The actual physical prescribed component is the original grouped wave,
including when the physical parameter point moves with the probe parameter.
The input buffer condition is imposed before the original ball is fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {m N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "d" => Fintype.card (Fin r × Bool)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace OriginalWaveSeedRescaledFamily

def physicalPairMap (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (u : Fin d → ℝ) (z : P × M) : V :=
  let Fz : Z → M → V := fun _ : Z => c • F
  let hz := fun _ : Z => contMDiff_const_rescale F hF c
  let cz : (l : Fin r) → Fin (family.refinement l).count → Z → D → M :=
    fun l s _ y => (family.outer l s).spatialChart.symm y
  let vz := fun l s => actualProbeNormalAmplitude Fz (cz l s)
    ((family.refinement l).cutoffCoordinates s)
    (fun _ y => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
      ((family.outer l s).spatialChart.symm y) ((waves l).normal ((family.outer l s).spatialChart.symm y)))
    delta tau (weight l)
  let R := jointGroupedParameterPrescribedAmplitude (round4PairedParameterIndex r).toEmbedding
    (fun _ : P => Fz 0) (fun _ => hz 0)
    (fun l s _ => cz l s 0) (fun l s _ => vz l s 0) tau length
    (fun l s => passiveParameterChart (0 : Z) (family.inner l s).chart)
  ∑ l, (Real.cos (weight l*(waves l).phase z.2/tau) • R false u l z -
    Real.sin (weight l*(waves l).phase z.2/tau) • R true u l z)

theorem physicalPairMap_eq_groupedPairMap
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (u : ProbeParameters r) (p : P) (x : M) :
    family.physicalPairMap c hc delta tau length
      (probeParameterEmbedding (round4PairedParameterIndex r).toEmbedding u) (p,x) =
      family.groupedPairMap c hc delta tau length u x := by
  unfold physicalPairMap groupedPairMap
  simp only [jointGroupedPrescribedWave]
  apply Finset.sum_congr rfl
  intro l _
  have hA (imag : Bool) := passiveGroupedPrescribed_amplitude
    (0 : Z) (round4PairedParameterIndex r).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun l s => fun _ : Z => fun y => (family.outer l s).spatialChart.symm y)
    (fun l s => actualProbeNormalAmplitude (fun _ : Z => c • F)
      (fun _ : Z => fun y => (family.outer l s).spatialChart.symm y)
      ((family.refinement l).cutoffCoordinates s)
      (fun _ y => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
        ((family.outer l s).spatialChart.symm y)
        ((waves l).normal ((family.outer l s).spatialChart.symm y)))
      delta tau (weight l)) tau length (fun l s => (family.inner l s).chart)
    imag l (probeParameterEmbedding (round4PairedParameterIndex r).toEmbedding u) p x
  rw [hA false, hA true]
  rfl

variable [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]

theorem physicalPairMap_centered_original_ball
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : ProbeParameters r)
    (hu : ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) (x : M) :
    let p := actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ (round4PairedParameterReindex r u)
    family.physicalPairMap c hc delta tau length
      (passiveOriginalSmallParameter B amplitude ha b p₀ p) (p,x) =
      family.groupedPairMap c hc delta tau length u x := by
  intro p
  have hv : ‖round4PairedParameterReindex r u‖ <
      actualRepairParameterRadius (tensorChartFamilyOfAtlas B) := by
    simpa only [LinearIsometryEquiv.norm_map] using hu
  have hi := passiveOriginalSmallParameter_original_ball_identity B amplitude ha hbuffer
    b p₀ hp₀ (round4PairedParameterReindex r u) hv
  change family.physicalPairMap c hc delta tau length
    (passiveOriginalSmallParameter B amplitude ha b p₀
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ (round4PairedParameterReindex r u))) (p,x) = _
  rw [hi,← globalWave_original_parameter_map_eq]
  exact family.physicalPairMap_eq_groupedPairMap c hc delta tau length u p x

theorem physicalPairMap_centered_original_germ
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : ProbeParameters r)
    (hu : ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) :
    (fun v : ProbeParameters r =>
      let p := actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ (round4PairedParameterReindex r v)
      fun x => family.physicalPairMap c hc delta tau length
        (passiveOriginalSmallParameter B amplitude ha b p₀ p) (p,x)) =ᶠ[𝓝 u]
      family.groupedPairMap c hc delta tau length := by
  have hm : u ∈ Metric.ball (0 : ProbeParameters r)
      (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) := by
    simpa only [Metric.mem_ball,dist_zero_right] using hu
  filter_upwards [Metric.isOpen_ball.mem_nhds hm] with v hv
  funext x
  exact family.physicalPairMap_centered_original_ball c hc delta tau length
    B amplitude ha hbuffer b p₀ hp₀ v
      (by simpa only [Metric.mem_ball,dist_zero_right] using hv) x

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.physicalPairMap_eq_groupedPairMap
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.physicalPairMap_centered_original_ball
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.physicalPairMap_centered_original_germ

