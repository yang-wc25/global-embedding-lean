import NormalPolar.ActualProbeSecondaryResponse

/-! The complete secondary responses vanish at the literal original scales. -/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar

/-- Both native secondary responses have the same relative order 38/5.
This identity uses the actual delta-squared output of the physical solver. -/
theorem actualProbeSecondary_scale_identities (t : ℝ) (ht : 0 < t) (C : ℝ) :
    C * (t ^ (10 : ℕ)) ^ 2 / t ^ ((6 : ℝ)/5) =
      t ^ ((56 : ℝ)/5) * (C * |t| ^ ((38 : ℝ)/5)) ∧
    C * (t ^ (10 : ℕ)) ^ 2 / (t ^ ((6 : ℝ)/5)) ^ 3 =
      t ^ ((44 : ℝ)/5) * (C * |t| ^ ((38 : ℝ)/5)) := by
  have htau : t ^ ((6 : ℝ)/5) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hv : C * (t ^ (10 : ℕ)) ^ 2 / t ^ ((6 : ℝ)/5) =
      (t ^ (10 : ℕ) * t ^ ((6 : ℝ)/5)) *
        (C * (t ^ (10 : ℕ) / (t ^ ((6 : ℝ)/5)) ^ 2)) := by
    field_simp
    <;> ring
  have hh : C * (t ^ (10 : ℕ)) ^ 2 / (t ^ ((6 : ℝ)/5)) ^ 3 =
      (t ^ (10 : ℕ) / t ^ ((6 : ℝ)/5)) *
        (C * (t ^ (10 : ℕ) / (t ^ ((6 : ℝ)/5)) ^ 2)) := by
    field_simp
    <;> ring
  rw [probe_delta_mul_tau_eq_value_scale t ht, probe_delta_div_tau_sq_eq_C3_scale t ht] at hv
  rw [probe_delta_div_tau_eq_sigma t ht, probe_delta_div_tau_sq_eq_C3_scale t ht] at hh
  simpa only [abs_of_pos ht] using And.intro hv hh

def actualProbeSecondaryModulus (C t : ℝ) : ℝ := C * |t| ^ ((38 : ℝ)/5)

theorem actualProbeSecondaryModulus_nonneg {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ actualProbeSecondaryModulus C t := by
  unfold actualProbeSecondaryModulus
  positivity

theorem actualProbeSecondaryModulus_tendsto (C : ℝ) :
    Tendsto (actualProbeSecondaryModulus C) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (actualProbeSecondaryModulus C) := by
    unfold actualProbeSecondaryModulus
    exact continuous_const.mul
      ((Real.continuous_rpow_const (by norm_num : 0 ≤ (38 : ℝ)/5)).comp continuous_abs)
  simpa [actualProbeSecondaryModulus,Real.zero_rpow (by norm_num : (38 : ℝ)/5 ≠ 0)] using
    (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

end GlobalEmbedding.NormalPolar

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N n j : ℕ} {Ep M Label Sub U E : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]

private local instance secondaryProbeScaleBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryProbeScaleBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance secondaryProbeScaleBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedSpace
private local instance secondaryProbeScaleResponseSemi :
    SeminormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryProbeScaleResponseNormed :
    NormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Original-scale responses of the SAME full signed secondary sum.
The constant is the explicit primitive cost of this observation, not an
assumed completed-wave or native-response budget. Uniform primitive costs
give the globally nonnegative vanishing modulus defined above. -/
theorem ActualSecondaryProbeObservation.native_paper_responses
    (F : Ep → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (Mg CH : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j (t^((11 : ℝ)/10)) Mg CH (t^(10 : ℕ)) W)
    (obs : ActualSecondaryProbeObservation F hF data (U × E))
    (length : ℕ) (hj : 3 ≤ j) (hbudget : j+1+length ≤ n)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (z : U × E) (hz : z ∈ obs.sample) (direction : U) :
    ‖fderiv ℝ (fun u => obs.wave (t^((6 : ℝ)/5)) length (u,z.2)) z.1 direction‖ ≤
      t ^ ((56 : ℝ)/5) * actualProbeSecondaryModulus (obs.cost length) t * ‖direction‖ ∧
    ‖fderiv ℝ (fun u => fderiv ℝ (fderiv ℝ
      (fun x => obs.wave (t^((6 : ℝ)/5)) length (u,x))) z.2) z.1 direction‖ ≤
      t ^ ((44 : ℝ)/5) * actualProbeSecondaryModulus (obs.cost length) t * ‖direction‖ := by
  obtain ⟨hell,hell1,htau,htaul⟩ := probe_original_scale_conditions t ht ht1
  have h := obs.native_responses (t^((6 : ℝ)/5)) length hj hbudget
    hell hell1 htau htaul hMg hCH hW z hz
  have he := actualProbeSecondary_scale_identities t ht (obs.cost length)
  rw [he.1] at h
  rw [he.2] at h
  constructor
  · exact (ContinuousLinearMap.le_opNorm _ direction).trans
      (mul_le_mul_of_nonneg_right h.1 (norm_nonneg direction))
  · exact (ContinuousLinearMap.le_opNorm _ direction).trans
      (mul_le_mul_of_nonneg_right h.2 (norm_nonneg direction))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.NormalPolar.actualProbeSecondary_scale_identities
#print axioms GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus_tendsto
#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.native_paper_responses
