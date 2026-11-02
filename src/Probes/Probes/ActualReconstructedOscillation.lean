import Probes.ActualReconstructedParameter
import Probes.ActualProbeHigherBounds

/-!
# Actual oscillating homogeneous correction

Source: the same finite reconstruction in (6.2) and the first probe step (8.3).
The original complex/real multiplier is reused after explicit Euclidean/Pi
target conversion. Both target operator norms are retained. Parameter response
is proved for the SAME reconstructed and modulated map.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Filter Set Function
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation

def euclideanTargetCoordinateCost (N : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖

theorem euclideanTargetCoordinateCost_nonneg (N : ℕ) :
    0 ≤ euclideanTargetCoordinateCost N := mul_nonneg (norm_nonneg _) (norm_nonneg _)

section FastTarget
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {N : ℕ}

/-- Exact real trigonometric modulation on the original Euclidean target. -/
def actualTrigModulation (sine : Bool) (phi : D → ℝ) (tau : ℝ)
    (R : D → EuclideanSpace ℝ (Fin N)) (x : D) : EuclideanSpace ℝ (Fin N) :=
  (if sine then Real.sin (phi x / tau) else Real.cos (phi x / tau)) • R x

/-- Smoothness uses the actual phase and amplitude on the original open set. -/
theorem actualTrigModulation_contDiffOn (sine : Bool) (phi : D → ℝ) (tau : ℝ)
    (R : D → EuclideanSpace ℝ (Fin N)) (O : Set D)
    (hphi : ContDiffOn ℝ ∞ phi O) (hR : ContDiffOn ℝ ∞ R O) :
    ContDiffOn ℝ ∞ (actualTrigModulation sine phi tau R) O := by
  cases sine
  · exact (hphi.div_const tau).cos.smul hR
  · exact (hphi.div_const tau).sin.smul hR

/-- The original fast multiplier controls the SAME native Euclidean wave.
No Euclidean/Pi isometry is asserted. -/
theorem actualTrigModulation_weighted_jet_bound
    (sine : Bool) (j n : ℕ) (hn : n ≤ j) (O : Set D) (hO : IsOpen O)
    (phi : D → ℝ) (R : D → EuclideanSpace ℝ (Fin N))
    (hphi : ContDiffOn ℝ ∞ phi O) (hR : ContDiffOn ℝ ∞ R O)
    (x : D) (hx : x ∈ O) (tau ell M K : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k+1) phi x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k R x‖ ≤ K) :
    tau ^ n * ‖iteratedFDeriv ℝ n (actualTrigModulation sine phi tau R) x‖ ≤
      euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j M * K := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let Rp := e ∘ R
  have hRp : ContDiffOn ℝ ∞ Rp O := e.contDiff.comp_contDiffOn hR
  have hRpbound : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k Rp x‖ ≤ ‖e.toContinuousLinearMap‖ * K := by
    intro k hk
    have h := e.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (hR.contDiffAt (hO.mem_nhds hx)) (n := k) (by simp)
    calc
      _ ≤ ell ^ k * (‖e.toContinuousLinearMap‖ * ‖iteratedFDeriv ℝ k R x‖) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (htau.le.trans htaul) k)
      _ = ‖e.toContinuousLinearMap‖ * (ell ^ k * ‖iteratedFDeriv ℝ k R x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hamp k hk) (norm_nonneg _)
  let W : D → Fin N → ℝ := fun y =>
    (if sine then Real.sin (phi y / tau) else Real.cos (phi y / tau)) • Rp y
  have hW : ContDiffOn ℝ ∞ W O := by
    cases sine
    · exact (hphi.div_const tau).cos.smul hRp
    · exact (hphi.div_const tau).sin.smul hRp
  have hb : tau ^ n * ‖iteratedFDeriv ℝ n W x‖ ≤
      incrementsFastMultiplierConstant j M * (‖e.toContinuousLinearMap‖ * K) := by
    cases sine
    · exact probe_cos_fast_jet_bound j n hn O hO phi Rp hphi hRp x hx
        tau ell M _ htau htaul hell1 (mul_nonneg (norm_nonneg _) hK) hphase hRpbound
    · exact probe_sin_fast_jet_bound j n hn O hO phi Rp hphi hRp x hx
        tau ell M _ htau htaul hell1 (mul_nonneg (norm_nonneg _) hK) hphase hRpbound
  have he : actualTrigModulation sine phi tau R = e.symm ∘ W := by
    funext y
    cases sine <;> simp [actualTrigModulation, W, Rp]
  rw [he]
  have hi := e.symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (hW.contDiffAt (hO.mem_nhds hx)) (n := n) (by simp)
  calc
    _ ≤ tau ^ n * (‖e.symm.toContinuousLinearMap‖ * ‖iteratedFDeriv ℝ n W x‖) :=
      mul_le_mul_of_nonneg_left hi (pow_nonneg htau.le n)
    _ = ‖e.symm.toContinuousLinearMap‖ * (tau ^ n * ‖iteratedFDeriv ℝ n W x‖) := by ring
    _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        (incrementsFastMultiplierConstant j M * (‖e.toContinuousLinearMap‖ * K)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by unfold euclideanTargetCoordinateCost; ring

end FastTarget

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ} [Fintype ι]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m+1) → ℂ

/-- Literal reconstructed correction with its actual sine or cosine factor. -/
def actualReconstructedWave (sine : Bool) (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : D → Cdata) : D → V :=
  actualTrigModulation sine phi tau (incrementsPrimaryReconstructedChannel F hF c channel tau p k)

/-- Modulation retains the actual native parameter derivative of the original
reconstruction; phase and geometry are fixed in this real parameter family. -/
theorem fderiv_actualReconstructedWave_column [DecidableEq ι]
    (sine : Bool) (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) (i : ι) :
    fderiv ℝ (fun w => actualReconstructedWave sine phi F hF c channel tau p
      (finiteProbeSource k w) x) u (Pi.single i 1) =
        actualReconstructedWave sine phi F hF c channel tau p (k i) x := by
  let a : ℝ := if sine then Real.sin (phi x / tau) else Real.cos (phi x / tau)
  have hd := hasFDerivAt_primaryReconstructedParameter F hF c channel tau p k O hO hA hB hk x hx u
  have hm := (hd.const_smul a).fderiv
  change fderiv ℝ (fun w => a • incrementsPrimaryReconstructedChannel F hF c channel tau p
    (finiteProbeSource k w) x) u = a • reconstructedParameterMap F hF c channel tau p k x at hm
  change fderiv ℝ (fun w => a • incrementsPrimaryReconstructedChannel F hF c channel tau p
    (finiteProbeSource k w) x) u (Pi.single i 1) = _
  rw [hm]
  have hc := fderiv_primaryReconstructedParameter_column F hF c channel tau p k O hO hA hB hk x hx u i
  rw [hd.fderiv] at hc
  change a • reconstructedParameterMap F hF c channel tau p k x (Pi.single i 1) =
    a • incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) x
  rw [hc]

/-- Spatial derivatives of the true parameter response are the derivatives of
the same actual modulated correction column on the original open chart. -/
theorem iteratedFDeriv_fderiv_actualReconstructedWave_column [DecidableEq ι]
    (sine : Bool) (phi : D → ℝ) (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O)
    (u : ι → ℝ) (i : ι) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ
      (fun w => actualReconstructedWave sine phi F hF c channel tau p
        (finiteProbeSource k w) y) u (Pi.single i 1)) x =
      iteratedFDeriv ℝ j (actualReconstructedWave sine phi F hF c channel tau p (k i)) x := by
  have he : (fun y => fderiv ℝ
      (fun w => actualReconstructedWave sine phi F hF c channel tau p
        (finiteProbeSource k w) y) u (Pi.single i 1))
      =ᶠ[𝓝 x] actualReconstructedWave sine phi F hF c channel tau p (k i) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact fderiv_actualReconstructedWave_column sine phi F hF c channel tau p k O hO hA hB hk y hy u i
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualTrigModulation_weighted_jet_bound
#print axioms GlobalEmbedding.Continuation.fderiv_actualReconstructedWave_column
#print axioms GlobalEmbedding.Continuation.iteratedFDeriv_fderiv_actualReconstructedWave_column
