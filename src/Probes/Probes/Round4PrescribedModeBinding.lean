import Probes.ActualPrescribedProbeFirstStep
import Probes.ActualSecondaryModulation
import GlobalEmbedding.Paper.IncrementsModeFullReconstruction

/-!
# The literal prescribed probe is the original full reconstructed mode

Source: (8.3) and the homogeneous case of (6.2).  This bridge retains the two
real normal amplitudes `u₁ vf` and `-u₂ vf`, the exact original complex source,
the finite mode polynomial, and the actual full reconstruction.  It permits
the physical linearized metric identity to be applied to the same probe whose
value and Hessian responses were already proved.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A single summand of the already-defined prescribed first block. -/
def round4ActualProbeMode
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (phi : D → ℝ) (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) (x : D) : V :=
  Real.cos (phi x/tau) • (u (label (l,false)) • (vf x : V)) -
    Real.sin (phi x/tau) • ((-u (label (l,true))) • (vf x : V)) +
    actualRealHomogeneousProbe phi F hF c tau length
      (actualPairedNormalSource label l F hF c vf u) x

/-- The actual paired source uses the same two normal amplitudes as the full
physical mode. No independent source or correction is introduced. -/
theorem round4ActualProbeMode_eq_full_reconstruction
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (phi : D → ℝ) (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) :
    let source := actualPairedNormalSource label l F hF c vf u
    let finiteU := incrementsActualModeSum (incrementsModeComplexFirstOrderA F hF c)
      (incrementsModeComplexFirstOrderB F hF c) ((tau : ℂ)/Complex.I) length source
    let ZR := incrementsModeFullReconstruction F hF c (incrementsModeRealPart ∘ finiteU)
      (fun _ _ _ => 0) (fun x => u (label (l,false)) • vf x)
    let ZI := incrementsModeFullReconstruction F hF c (incrementsModeImagPart ∘ finiteU)
      (fun _ _ _ => 0) (fun x => (-u (label (l,true))) • vf x)
    round4ActualProbeMode label l F hF c vf phi tau length u =
      actualSecondaryModulation phi tau ZR ZI := by
  intro source finiteU ZR ZI
  funext x
  have hz : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) x = 0 := by
    ext q
    simp [incrementsModeTransverseSource]
  simp only [round4ActualProbeMode,actualSecondaryModulation,ZR,ZI,
    incrementsModeFullReconstruction,hz,map_zero,Submodule.coe_zero,smul_zero,sub_zero,
    actualRealHomogeneousProbe,actualReconstructedWave,actualTrigModulation,
    Bool.false_eq_true,ite_false,ite_true,incrementsPrimaryReconstructedChannel,
    Function.comp_def,Submodule.coe_smul,source,finiteU]
  module

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "X" => Ep × D

/-- Every literal `(8.3)` summand is the same full reconstructed mode. The
two negative value columns and the negative imaginary source are unchanged. -/
theorem actualPrescribedProbeFirstBlock_eq_sum_actual_modes
    (label : (Fin r × Bool) ↪ Fin p) (delta tau : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (length : ℕ) (b : Ep) (u : Fin p → ℝ) (x : D) :
    actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu length b u x =
      ∑ l, round4ActualProbeMode label l (F b) (hF b) (chart b)
        (actualProbeNormalAmplitude F chart (chi l) (nu l) delta tau (weight l) b)
        (fun y => weight l*phase l y) tau length u x := by
  rw [actualPrescribedProbeFirstBlock_eq, actualFiniteProbeDisplacement_eq_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [round4ActualProbeMode,actualProbeCosColumn,actualProbeSinColumn,
    probeFastPhase_eq,actualProbeNormalAmplitude,Submodule.coe_smul,neg_div]
  module

/-- The primitive legal-normal condition supplies both full-mode kernel
conditions after multiplication by the actual prescribed amplitude. -/
theorem actualProbeNormalAmplitude_transverse_kernel
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (delta tau lam : ℝ) (z : X)
    (hlegal : incrementsTransversePairing (F z.1) (hF z.1) (chart z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1) z.2 a.succ)
      (nu z.1 z.2) = 0) (u : ℝ) :
    incrementsTransversePairing (F z.1) (hF z.1) (chart z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1) z.2 a.succ)
      (u • actualProbeNormalAmplitude F chart chi nu delta tau lam z.1 z.2) = 0 := by
  simp only [actualProbeNormalAmplitude,map_smul,hlegal,smul_zero]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4ActualProbeMode_eq_full_reconstruction
#print axioms GlobalEmbedding.Continuation.actualPrescribedProbeFirstBlock_eq_sum_actual_modes
#print axioms GlobalEmbedding.Continuation.actualProbeNormalAmplitude_transverse_kernel
