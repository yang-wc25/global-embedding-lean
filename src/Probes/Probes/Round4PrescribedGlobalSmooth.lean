import Probes.Round4PrescribedGlobalParity
import Probes.ActualJointHomogeneousParameter
import GlobalEmbedding.Paper.IncrementsModeSupportedChartPullback

/-!
# Genuine joint smoothness of the complete globally extended prescribed modes

The original conditional chart extension is used unchanged. Its support and
smoothness follow from primitive normal-source support, the original spatial
finite solver, and the actual chart. Exact parameter columns then yield joint
smoothness in the external probe parameter, auxiliary parameters, and space.
No desired output regularity or support is assumed.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ
local notation "Cdata" => Fin (m+1) → ℂ

theorem round4_prescribed_amplitude_joint_contDiffOn
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 a : V)) O)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O) (u : Pspace) :
    ContDiffOn ℝ ∞ (fun z : X =>
      round4PrescribedAmplitude imag label l (F z.1) (hF z.1) (c z.1) (vf z.1) tau length u z.2) O := by
  let s := actualHomogeneousSource F hF c vf
  have hs : ContDiffOn ℝ ∞ s O := by
    let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
    let L := (2 : ℝ) • incrementsModeComplexInclude (m := m)
    have hh := L.contDiff.comp_contDiffOn ((Q.contDiff.comp_contDiffOn hBR).clm_apply hvf)
    apply hh.congr
    intro z hz
    exact actualHomogeneousSource_eq F hF c vf z
  let su := fun z : X => actualPairedNormalSource label l (F z.1) (hF z.1) (c z.1) (vf z.1) u z.2
  have hsu : ContDiffOn ℝ ∞ su O := by
    have hh : ContDiffOn ℝ ∞ (finiteProbeSource (pairedProbeSourceDictionary label l s) u) O := by
      exact ContDiffOn.sum (fun q _ =>
        (pairedProbeSourceDictionary_contDiffOn label l s O hs q).const_smul (u q))
    apply hh.congr
    intro z hz
    exact congrFun (actualPairedNormalSource_eq_finite_source label l (F z.1) (hF z.1)
      (c z.1) (vf z.1) u) z.2
  let channel : Cdata →L[ℝ] D := if imag then incrementsModeImagPart else incrementsModeRealPart
  let U := fun b => incrementsActualModeSum (incrementsModeComplexFirstOrderA (F b) (hF b) (c b))
    (incrementsModeComplexFirstOrderB (F b) (hF b) (c b)) ((tau:ℂ)/Complex.I) length
    (fun x => su (b,x))
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O :=
    actual_joint_mode_sum_contDiffOn F hF c su tau length O hO hA hB hsu
  have hu := channel.contDiff.comp_contDiffOn hU
  have hd := (incrementsJointSpatialJets_bridge _ O hO hu).2.1
  have ht : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseTensor (F z.1) (c z.1) (channel ∘ U z.1) z.2) O := by
    exact ((hT.clm_apply hu).add (contDiffOn_const.clm_apply hd)).congr
      (fun z _ => incrementsModeTransverseTensor_split (F z.1) (c z.1) (channel ∘ U z.1) z.2)
  have hR := (hG.clm_apply hu).add (hJ.clm_apply ht)
  exact (hvf.const_smul (if imag then -u (label (l,true)) else u (label (l,false)))).add hR

/-- Fixed-u smoothness and support of the original complete chart extension. -/
theorem round4_prescribed_global_amplitude_smooth
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (W K : Set (Ep × M)) (hW : IsOpen W)
    (hK : IsClosed (Subtype.val ⁻¹' K : Set W)) (hKsource : K ⊆ a.source)
    (hchart : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ a a.source)
    (hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 k : V)) a.target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target)
    (hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K)
    (u : Pspace) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞
      (round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u) W ∧
    tsupport (fun y : W => round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u y) ⊆
      Subtype.val ⁻¹' K := by
  let Z := fun z : X => round4PrescribedAmplitude imag label l
    (F z.1) (hF z.1) (c z.1) (vf z.1) tau length u z.2
  have hZ := round4_prescribed_amplitude_joint_contDiffOn imag label l F hF c vf tau length
    a.target a.open_target hA hB hG hJ hT hBR hvf u
  apply increments_supported_smooth_chart_pullback a W K hW hK hKsource hchart Z hZ
  intro y hy hn
  change round4PrescribedAmplitude imag label l (F (a y).1) (hF (a y).1)
    (c (a y).1) (vf (a y).1) tau length u (a y).2 = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hv : (a y).2 ∈ tsupport (fun x => (vf (a y).1 x : V)) :=
    round4PrescribedAmplitude_tsupport imag label l (F (a y).1) (hF (a y).1)
      (c (a y).1) (vf (a y).1) tau length u hs
  have hvj : a y ∈ tsupport (fun z : X => (vf z.1 z.2 : V)) :=
    tsupport_comp_subset_preimage _ (f := fun x : D => ((a y).1,x))
      (continuous_const.prodMk continuous_id) hv
  exact hn (by simpa only [a.left_inv hy] using hinput (a y) (a.map_source hy) hvj)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_amplitude_joint_contDiffOn
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_amplitude_smooth
