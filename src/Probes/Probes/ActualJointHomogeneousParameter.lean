import Probes.ActualJointHomogeneousOscillation
import Probes.ActualFullProbeJointSmooth
import Probes.ActualEuclideanProbeHigherBounds

/-!
# Actual homogeneous correction: all auxiliary jets and native probe responses

Every field below is the literal original finite solver followed by its original
two-channel reconstruction. The auxiliary parameter is retained in all joint
derivatives. Linearity in the separate finite probe parameter is proved from
source superposition on the actual open slice, then transferred to joint germs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} [Fintype ι]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

omit [Fintype ι] in
/-- Restriction of a genuine joint field to an auxiliary-parameter slice. -/
theorem actual_joint_contDiffOn_slice {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (O : Set X) (hf : ContDiffOn ℝ ∞ f O) (b : Ep) :
    ContDiffOn ℝ ∞ (fun x : D => f (b,x)) ((fun x : D => (b,x)) ⁻¹' O) :=
  hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)

/-- Smoothness of the same finite spatial solver in all auxiliary directions.
This statement has no numerical budgets, scale restrictions, or output inputs. -/
theorem actual_joint_mode_sum_contDiffOn
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (source : X → Cdata) (tau : ℝ) (length : ℕ)
    (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hs : ContDiffOn ℝ ∞ source O) :
    ContDiffOn ℝ ∞ (fun z : X => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1))
      (incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1))
      ((tau : ℂ)/Complex.I) length (fun x => source (z.1,x)) z.2) O := by
  let A := fun b => incrementsModeComplexFirstOrderA (F b) (hF b) (c b)
  let B := fun b => incrementsModeComplexFirstOrderB (F b) (hF b) (c b)
  let alpha := (tau : ℂ)/Complex.I
  have hit (q : ℕ) : ContDiffOn ℝ ∞ (fun z : X =>
      ((incrementsActualModeStep (A z.1) (B z.1) alpha)^[q]
        (fun x => source (z.1,x))) z.2) O := by
    induction q with
    | zero => exact hs
    | succ q ih =>
      have hd := (incrementsJointSpatialJets_bridge _ O hO ih).2.1
      simpa only [Function.iterate_succ_apply',incrementsActualModeStep,
        incrementsActualFirstOrder] using
        ((hB.clm_apply ih).add (hA.clm_apply hd)).const_smul (-alpha)
  exact (ContDiffOn.sum fun q _ => hit q).const_smul alpha

/-- Joint smoothness of the actual homogeneous wave, including auxiliary b. -/
theorem actual_joint_homogeneous_wave_contDiffOn
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (source : X → Cdata) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hs : ContDiffOn ℝ ∞ source O) (hphase : ContDiffOn ℝ ∞ phase O) :
    ContDiffOn ℝ ∞ (fun z : X => actualRealHomogeneousProbe (fun x => phase (z.1,x))
      (F z.1) (hF z.1) (c z.1) tau length (fun x => source (z.1,x)) z.2) O := by
  let U := fun b => incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F b) (hF b) (c b))
    (incrementsModeComplexFirstOrderB (F b) (hF b) (c b))
    ((tau : ℂ)/Complex.I) length (fun x => source (b,x))
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O :=
    actual_joint_mode_sum_contDiffOn F hF c source tau length O hO hA hB hs
  have hR (channel : Cdata →L[ℝ] D) : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeReconstruction (F z.1) (hF z.1) (c z.1)
        (channel ∘ U z.1) z.2) O := by
    have hu := channel.contDiff.comp_contDiffOn hU
    have hd := (incrementsJointSpatialJets_bridge _ O hO hu).2.1
    have ht : ContDiffOn ℝ ∞ (fun z : X =>
        incrementsModeTransverseTensor (F z.1) (c z.1) (channel ∘ U z.1) z.2) O := by
      exact ((hT.clm_apply hu).add (contDiffOn_const.clm_apply hd)).congr
        (fun z _ => incrementsModeTransverseTensor_split (F z.1) (c z.1)
          (channel ∘ U z.1) z.2)
    exact (hG.clm_apply hu).add (hJ.clm_apply ht)
  exact actualSecondaryModulation_contDiffOn phase tau _ _ O hphase
    (hR incrementsModeRealPart) (hR incrementsModeImagPart)

/-- Actual finite source superposition on the original joint open set. -/
theorem actual_joint_homogeneous_wave_finite_source [DecidableEq ι]
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (source : ι → X → Cdata) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hs : ∀ q, ContDiffOn ℝ ∞ (source q) O)
    (z : X) (hz : z ∈ O) (u : ι → ℝ) :
    actualRealHomogeneousProbe (fun x => phase (z.1,x))
      (F z.1) (hF z.1) (c z.1) tau length
      (fun x => finiteProbeSource source u (z.1,x)) z.2 =
    finiteProbeSource (fun q (w : X) => actualRealHomogeneousProbe
      (fun x => phase (w.1,x)) (F w.1) (hF w.1) (c w.1) tau length
      (fun x => source q (w.1,x)) w.2) u z := by
  have hslice : ContDiff ℝ ∞ (fun x : D => (z.1,x)) :=
    contDiff_const.prodMk contDiff_id
  have hAs : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1))
      ((fun x : D => (z.1,x)) ⁻¹' O) :=
    actual_joint_contDiffOn_slice _ O hA z.1
  have hBs : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1))
      ((fun x : D => (z.1,x)) ⁻¹' O) :=
    actual_joint_contDiffOn_slice _ O hB z.1
  have hss (q : ι) : ContDiffOn ℝ ∞ (fun x : D => source q (z.1,x))
      ((fun x : D => (z.1,x)) ⁻¹' O) :=
    actual_joint_contDiffOn_slice _ O (hs q) z.1
  have he := actualRealHomogeneousProbe_finite_source (fun x => phase (z.1,x))
    (F z.1) (hF z.1) (c z.1)
    tau length (fun q x => source q (z.1,x)) ((fun x : D => (z.1,x)) ⁻¹' O)
    (hO.preimage hslice.continuous) hAs hBs hss z.2 hz u
  rw [show finiteProbeSource (fun q x => source q (z.1,x)) u =
    (fun x => finiteProbeSource source u (z.1,x)) from rfl] at he
  simpa only [finiteProbeSource] using he

/-- All native joint (b,x) derivatives of the same correction are exactly
linear in the actual finite source parameter u. -/
theorem actual_joint_homogeneous_wave_jet [DecidableEq ι]
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (source : ι → X → Cdata) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hs : ∀ q, ContDiffOn ℝ ∞ (source q) O) (hphase : ContDiffOn ℝ ∞ phase O)
    (z : X) (hz : z ∈ O) (u : ι → ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (fun w : X => actualRealHomogeneousProbe
      (fun x => phase (w.1,x)) (F w.1) (hF w.1) (c w.1) tau length
      (fun x => finiteProbeSource source u (w.1,x)) w.2) z =
    probeColumnMap (fun q => iteratedFDeriv ℝ j (fun w : X => actualRealHomogeneousProbe
      (fun x => phase (w.1,x)) (F w.1) (hF w.1) (c w.1) tau length
      (fun x => source q (w.1,x)) w.2) z) u := by
  let columns := fun q (w : X) => actualRealHomogeneousProbe (fun x => phase (w.1,x))
    (F w.1) (hF w.1) (c w.1) tau length (fun x => source q (w.1,x)) w.2
  have he : (fun w : X => actualRealHomogeneousProbe (fun x => phase (w.1,x))
      (F w.1) (hF w.1) (c w.1) tau length
      (fun x => finiteProbeSource source u (w.1,x)) w.2) =ᶠ[𝓝 z]
      finiteProbeSource columns u := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact actual_joint_homogeneous_wave_finite_source F hF c source phase tau length
      O hO hA hB hs w hw u
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply iteratedFDeriv_finiteProbeSource
  intro q
  exact ((actual_joint_homogeneous_wave_contDiffOn F hF c (source q) phase tau length
    O hO hA hB hG hJ hT (hs q) hphase).contDiffAt (hO.mem_nhds hz)).of_le (by simp)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_mode_sum_contDiffOn
#print axioms GlobalEmbedding.Continuation.actual_joint_homogeneous_wave_contDiffOn
#print axioms GlobalEmbedding.Continuation.actual_joint_homogeneous_wave_jet
