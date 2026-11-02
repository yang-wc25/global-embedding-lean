import Probes.ActualReconstructedWaveBounds
import Probes.ActualProbeConnectionResponse
import GlobalEmbedding.Paper.IncrementsPrimaryWaveFirstJet

/-!
# The actual two-channel homogeneous real probe correction

The correction is the real part of the ORIGINAL reconstructed complex mode:
cos(phi/tau) R(real u) - sin(phi/tau) R(imag u). Both channels are retained.
Native parameter derivatives before and after every spatial jet are proved
from the actual finite solver's linear source superposition, on the original
open chart. No mixed derivative interchange or correction formula is assumed.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Filter Set Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Offline

section FiniteJets
variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

/-- A native finite parameter map for arbitrary actual source columns. -/
def probeColumnMap (g : ι → Y) : (ι → ℝ) →L[ℝ] Y :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (g i)

theorem probeColumnMap_apply (g : ι → Y) (u : ι → ℝ) :
    probeColumnMap g u = ∑ i, u i • g i := by simp [probeColumnMap]

theorem probeColumnMap_column [DecidableEq ι] (g : ι → Y) (i : ι) :
    probeColumnMap g (Pi.single i 1) = g i := by
  simp [probeColumnMap, Pi.single_apply]

/-- True spatial jets of a finite real source span. -/
theorem iteratedFDeriv_finiteProbeSource (g : ι → X → Y) (u : ι → ℝ) (n : ℕ) (x : X)
    (hg : ∀ i, ContDiffAt ℝ n (g i) x) :
    iteratedFDeriv ℝ n (finiteProbeSource g u) x =
      probeColumnMap (fun i ↦ iteratedFDeriv ℝ n (g i) x) u := by
  rw [probeColumnMap_apply]
  change iteratedFDeriv ℝ n (fun y ↦ ∑ i, u i • g i y) x = _
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ (hg i).const_smul (u i))]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedFDeriv_const_smul_apply' (hg i)

end FiniteJets

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ} [Fintype ι]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The actual real homogeneous correction with BOTH reconstructed channels. -/
def actualRealHomogeneousProbe (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (tau : ℝ) (p : ℕ) (k : D → Cdata) : D → V := fun x ↦
  actualReconstructedWave false phi F hF c incrementsModeRealPart tau p k x -
    actualReconstructedWave true phi F hF c incrementsModeImagPart tau p k x

/-- Exact identification with the original complex-to-real oscillatory mode. -/
theorem actualRealHomogeneousProbe_eq_original_mode
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : D → Cdata) :
    actualRealHomogeneousProbe phi F hF c tau p k = fun y ↦ WithLp.toLp 2
      (fun a : Fin N ↦ (Complex.exp (((phi y / tau : ℝ) : ℂ) * Complex.I) *
        ((incrementsPrimaryReconstructedChannel F hF c incrementsModeRealPart tau p k y a : ℂ) +
          Complex.I * (incrementsPrimaryReconstructedChannel F hF c
            incrementsModeImagPart tau p k y a : ℂ))).re) := by
  exact (increments_primary_real_mode_eq phi tau
    (incrementsPrimaryReconstructedChannel F hF c incrementsModeRealPart tau p k)
    (incrementsPrimaryReconstructedChannel F hF c incrementsModeImagPart tau p k)).symm

/-- Smoothness comes from the original finite solver and actual geometric fields. -/
theorem actualRealHomogeneousProbe_contDiffOn
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : D → Cdata)
    (O : Set D) (hO : IsOpen O) (hphi : ContDiffOn ℝ ∞ phi O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ContDiffOn ℝ ∞ k O) :
    ContDiffOn ℝ ∞ (actualRealHomogeneousProbe phi F hF c tau p k) O := by
  exact (actualTrigModulation_contDiffOn false phi tau _ O hphi
    (increments_primary_reconstructed_channel_contDiffOn F hF c incrementsModeRealPart
      tau p k O hO hA hB hG hJ hT0 hk)).sub
    (actualTrigModulation_contDiffOn true phi tau _ O hphi
    (increments_primary_reconstructed_channel_contDiffOn F hF c incrementsModeImagPart
      tau p k O hO hA hB hG hJ hT0 hk))

/-- The SAME two-channel correction preserves the actual finite source span. -/
theorem actualRealHomogeneousProbe_finite_source [DecidableEq ι]
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k u) x =
      finiteProbeSource (fun i ↦ actualRealHomogeneousProbe phi F hF c tau p (k i)) u x := by
  unfold actualRealHomogeneousProbe actualReconstructedWave actualTrigModulation
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [primaryReconstructedParameter_eq_sum F hF c incrementsModeRealPart tau p k
    O hO hA hB hk x hx u,
    primaryReconstructedParameter_eq_sum F hF c incrementsModeImagPart tau p k O hO hA hB hk x hx u]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, finiteProbeSource]
  apply Finset.sum_congr rfl
  intro i _
  module

/-- Native parameter derivative of the actual original real correction. -/
theorem hasFDerivAt_actualRealHomogeneousProbe [DecidableEq ι]
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    HasFDerivAt (fun w ↦ actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k w) x)
      (probeColumnMap (fun i ↦ actualRealHomogeneousProbe phi F hF c tau p (k i) x)) u := by
  have heq : (fun w ↦ actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k w) x) =
      probeColumnMap (fun i ↦ actualRealHomogeneousProbe phi F hF c tau p (k i) x) := by
    funext w
    rw [actualRealHomogeneousProbe_finite_source phi F hF c tau p k O hO hA hB hk x hx w]
    exact (probeColumnMap_apply _ w).symm
  rw [heq]
  exact (probeColumnMap _).hasFDerivAt

/-- Every true spatial jet remains linear in the actual source parameters.
The equality is proved using only germs of the original solver on O. -/
theorem actualRealHomogeneousProbe_spatial_jet [DecidableEq ι]
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O) (hphi : ContDiffOn ℝ ∞ phi O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O)
    (x : D) (hx : x ∈ O) (u : ι → ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k u)) x =
      probeColumnMap (fun i ↦ iteratedFDeriv ℝ j
        (actualRealHomogeneousProbe phi F hF c tau p (k i)) x) u := by
  have he : actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k u) =ᶠ[𝓝 x]
      finiteProbeSource (fun i ↦ actualRealHomogeneousProbe phi F hF c tau p (k i)) u := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact actualRealHomogeneousProbe_finite_source phi F hF c tau p k O hO hA hB hk y hy u
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply iteratedFDeriv_finiteProbeSource
  intro i
  exact ((actualRealHomogeneousProbe_contDiffOn phi F hF c tau p (k i)
    O hO hphi hA hB hG hJ hT0 (hk i)).contDiffAt (hO.mem_nhds hx)).of_le (by simp)

/-- Parameter differentiation AFTER the actual spatial jet, without assuming
commutation of derivatives. The same original correction columns occur. -/
theorem hasFDerivAt_actualRealHomogeneousProbe_spatial_jet [DecidableEq ι]
    (phi : D → ℝ) (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F)
    (c : D → M) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O) (hphi : ContDiffOn ℝ ∞ phi O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O)
    (x : D) (hx : x ∈ O) (u : ι → ℝ) (j : ℕ) :
    HasFDerivAt (fun w ↦ iteratedFDeriv ℝ j
      (actualRealHomogeneousProbe phi F hF c tau p (finiteProbeSource k w)) x)
      (probeColumnMap (fun i ↦ iteratedFDeriv ℝ j
        (actualRealHomogeneousProbe phi F hF c tau p (k i)) x)) u := by
  have heq := funext (fun w ↦ actualRealHomogeneousProbe_spatial_jet phi F hF c tau p k
    O hO hphi hA hB hG hJ hT0 hk x hx w j)
  rw [heq]
  exact (probeColumnMap _).hasFDerivAt

#print axioms actualRealHomogeneousProbe_eq_original_mode
#print axioms actualRealHomogeneousProbe_finite_source
#print axioms hasFDerivAt_actualRealHomogeneousProbe_spatial_jet
end GlobalEmbedding.Offline
