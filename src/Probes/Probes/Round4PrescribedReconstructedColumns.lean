import Probes.Round4PrescribedModeBinding
import Probes.ActualReconstructedParameter
import GlobalEmbedding.Paper.IncrementsActualFullMeanCoefficient

/-!
# The complete prescribed amplitudes, including the real reconstruction

Both amplitudes contain the original normal term and the original finite
reconstruction.  The sparse paired source supplies their genuine parameter
columns.  Their support is derived from the primitive normal field, and
smoothness is derived from the original geometric coefficient fields.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m+1) → ℂ

def round4PrescribedAmplitude (imag : Bool)
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) (x : D) : V :=
  (if imag then -u (label (l,true)) else u (label (l,false))) • (vf x : V) +
    incrementsPrimaryReconstructedChannel F hF c
      (if imag then incrementsModeImagPart else incrementsModeRealPart) tau length
      (actualPairedNormalSource label l F hF c vf u) x

theorem round4ActualProbeMode_eq_amplitudes
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (phi : D → ℝ) (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) (x : D) :
    round4ActualProbeMode label l F hF c vf phi tau length u x =
      Real.cos (phi x/tau) • round4PrescribedAmplitude false label l F hF c vf tau length u x -
        Real.sin (phi x/tau) • round4PrescribedAmplitude true label l F hF c vf tau length u x := by
  simp only [round4ActualProbeMode,round4PrescribedAmplitude,actualRealHomogeneousProbe,
    actualReconstructedWave,actualTrigModulation,Bool.false_eq_true,ite_false,ite_true]
  module

theorem round4PrescribedAmplitude_finite_source
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hs : ContDiffOn ℝ ∞ (fun x => incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vf x)) O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    round4PrescribedAmplitude imag label l F hF c vf tau length u x =
      finiteProbeSource (fun q => round4PrescribedAmplitude imag label l F hF c vf tau length
        (Pi.single q 1)) u x := by
  classical
  let source := fun x => incrementsModeComplexInclude
    (incrementsModeSource F hF c (fun _ _ _ => 0) vf x)
  let k := pairedProbeSourceDictionary label l source
  have hk (q : Fin p) : ContDiffOn ℝ ∞ (k q) O :=
    pairedProbeSourceDictionary_contDiffOn label l source O hs q
  have hcol (q : Fin p) : actualPairedNormalSource label l F hF c vf (Pi.single q 1) = k q := by
    rw [actualPairedNormalSource_eq_finite_source]
    funext y
    simp [finiteProbeSource,k,source,Pi.single_apply]
  have hr := primaryReconstructedParameter_eq_sum F hF c
    (if imag then incrementsModeImagPart else incrementsModeRealPart)
    tau length k O hO hA hB hk x hx u
  have hsource : actualPairedNormalSource label l F hF c vf u = finiteProbeSource k u :=
    actualPairedNormalSource_eq_finite_source label l F hF c vf u
  simp only [round4PrescribedAmplitude,hsource,hcol,hr,finiteProbeSource,
    smul_add,Finset.sum_add_distrib]
  congr 1
  cases imag <;> simp [Pi.single_apply]

/-- The unscaled original homogeneous source is smooth from the true-B rows
and the primitive actual normal field. -/
theorem round4_actual_homogeneous_source_smooth
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (O : Set D)
    (hBR : ContDiffOn ℝ ∞ (fun x => fun i : Fin (m+1) =>
      (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hvf : ContDiffOn ℝ ∞ (fun x => (vf x : V)) O) :
    ContDiffOn ℝ ∞ (fun x => incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vf x)) O := by
  let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
  let L := (2 : ℝ) • incrementsModeComplexInclude (m := m)
  have hh := L.contDiff.comp_contDiffOn ((Q.contDiff.comp_contDiffOn hBR).clm_apply hvf)
  apply hh.congr
  intro x hx
  rw [actual_homogeneous_source_real_eq,map_smul]
  rfl

theorem round4PrescribedAmplitude_contDiffOn
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun x => freeGramRightInverse (fderiv ℝ (F ∘ c) x)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x => (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hT : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hBR : ContDiffOn ℝ ∞ (fun x => fun i : Fin (m+1) =>
      (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hvf : ContDiffOn ℝ ∞ (fun x => (vf x : V)) O) (u : Fin p → ℝ) :
    ContDiffOn ℝ ∞ (round4PrescribedAmplitude imag label l F hF c vf tau length u) O := by
  have hs := round4_actual_homogeneous_source_smooth F hF c vf O hBR hvf
  have hu : ContDiffOn ℝ ∞ (actualPairedNormalSource label l F hF c vf u) O := by
    rw [actualPairedNormalSource_eq_finite_source]
    unfold finiteProbeSource
    exact ContDiffOn.sum (fun q _ =>
      (pairedProbeSourceDictionary_contDiffOn label l _ O hs q).const_smul (u q))
  exact (hvf.const_smul _).add (increments_primary_reconstructed_channel_contDiffOn
    F hF c _ tau length _ O hO hA hB hG hJ hT hu)

theorem round4PairedNormalSource_tsupport
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (u : Fin p → ℝ) :
    tsupport (actualPairedNormalSource label l F hF c vf u) ⊆
      tsupport (fun x => (vf x : V)) := by
  apply closure_mono
  intro x hx
  by_contra hv
  have hv0 : (vf x : V) = 0 := by simpa only [mem_support,not_not] using hv
  apply hx
  have hs : incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vf x) = 0 := by
    rw [actual_homogeneous_source_real_eq,hv0,map_zero,smul_zero,map_zero]
  rw [actualPairedNormalSource_eq_finite_source,finiteProbeSource_paired_dictionary,hs]
  simp

/-- No support of the reconstructed amplitude is postulated: it follows from
the actual primitive normal-field support and locality of the original solver. -/
theorem round4PrescribedAmplitude_tsupport
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) :
    tsupport (round4PrescribedAmplitude imag label l F hF c vf tau length u) ⊆
      tsupport (fun x => (vf x : V)) := by
  unfold round4PrescribedAmplitude
  apply (tsupport_add _ _).trans
  exact union_subset (tsupport_smul_subset_right _ _)
    ((actual_full_mean_channel_support F hF c _ tau length _).trans
      (round4PairedNormalSource_tsupport label l F hF c vf u))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4ActualProbeMode_eq_amplitudes
#print axioms GlobalEmbedding.Continuation.round4PrescribedAmplitude_finite_source
#print axioms GlobalEmbedding.Continuation.round4PrescribedAmplitude_contDiffOn
#print axioms GlobalEmbedding.Continuation.round4PrescribedAmplitude_tsupport
