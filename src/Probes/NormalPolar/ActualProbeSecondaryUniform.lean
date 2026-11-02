import NormalPolar.ActualProbeSecondaryScales

/-!
# Uniform genuine secondary responses from fixed primitive profiles

All cost data are fixed before the physical family, scale and observer.
The observer may depend on the scale; its transition profile and active
multiplicities are tied to the fixed data. This proves that the response
modulus has a single constant, instead of treating a scale-dependent
observation cost as constant. The middle parameter/spatial derivative is
also estimated from the actual total second derivative.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
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

private local instance secondaryUniformBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryUniformBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance secondaryUniformBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedSpace
private local instance secondaryUniformResponseSemi :
    SeminormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryUniformResponseNormed :
    NormedAddCommGroup (U →L[ℝ] E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem ActualSecondaryProbeObservation.cost_eq_of_profiles
    {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    {data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W}
    (obs : ActualSecondaryProbeObservation F hF data (U × E))
    (length L R : ℕ) (T : ℕ → ℝ)
    (hT : obs.transitionCost = T) (hL : obs.primaryCount = L) (hR : obs.secondaryCount = R) :
    obs.cost length = actualConstructedSecondaryWaveBudget m N n j length L R Mg CH T := by
  unfold ActualSecondaryProbeObservation.cost
  rw [hT,hL,hR]

/-- The true mixed first spatial response costs two total derivatives of
the same completed secondary wave. -/
theorem ActualSecondaryProbeObservation.native_first_response
    {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    {data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W}
    (obs : ActualSecondaryProbeObservation F hF data (U × E))
    (tau : ℝ) (length : ℕ) (hj : 2 ≤ j) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (z : U × E) (hz : z ∈ obs.sample) :
    ‖fderiv ℝ (fun u => fderiv ℝ (fun x => obs.wave tau length (u,x)) z.2) z.1‖ ≤
      obs.cost length * delta ^ 2 / tau ^ 2 := by
  have hs := obs.wave_smooth tau length hW
  have hb := obs.weighted_jets tau length hbudget hell hell1 htau htaul hMg hCH hW
  have hd := actual_parameter_spatial_first_jet_le obs.domain_open hs (obs.sample_subset hz) 0
  simp only [norm_iteratedFDeriv_zero,Nat.zero_add] at hd
  exact hd.trans ((le_div_iff₀ (pow_pos htau 2)).2 (by
    simpa only [mul_comm] using hb 2 hj z hz))

/-- A fixed primitive cost supplies a globally nonnegative vanishing
modulus for all three native responses of every actual observation family.
In particular no chosen physical array at a fixed external parameter is
silently differentiated: U is the actual first observer factor. -/
theorem actual_secondary_native_paper_responses_uniform
    (length L R : ℕ) (T : ℕ → ℝ) (Mg CH : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (hj : 3 ≤ j) (hbudget : j+1+length ≤ n) :
    let C := actualConstructedSecondaryWaveBudget m N n j length L R Mg CH T
    0 ≤ C ∧
    (∀ t, 0 ≤ actualProbeSecondaryModulus C t) ∧
    Tendsto (actualProbeSecondaryModulus C) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (F : Ep → M → EuclideanSpace ℝ (Fin N))
      (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
        𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
      (t : ℝ), 0 < t → t ≤ 1 → ∀ (W : Set (Ep × M)), IsOpen W →
    ∀ (data : ActualSecondarySignedRecord Label → Sub →
        ActualSecondaryPhysicalPieceData F hF n j (t^((11 : ℝ)/10)) Mg CH (t^(10 : ℕ)) W)
      (obs : ActualSecondaryProbeObservation F hF data (U × E)),
      obs.transitionCost = T → obs.primaryCount = L → obs.secondaryCount = R →
    ∀ z ∈ obs.sample, ∀ direction : U,
      ‖fderiv ℝ (fun u => obs.wave (t^((6 : ℝ)/5)) length (u,z.2)) z.1 direction‖ ≤
        t^((56 : ℝ)/5) * actualProbeSecondaryModulus C t * ‖direction‖ ∧
      ‖fderiv ℝ (fun u => fderiv ℝ (fun x =>
        obs.wave (t^((6 : ℝ)/5)) length (u,x)) z.2) z.1 direction‖ ≤
        t^(10 : ℕ) * actualProbeSecondaryModulus C t * ‖direction‖ ∧
      ‖fderiv ℝ (fun u => fderiv ℝ (fderiv ℝ
        (fun x => obs.wave (t^((6 : ℝ)/5)) length (u,x))) z.2) z.1 direction‖ ≤
        t^((44 : ℝ)/5) * actualProbeSecondaryModulus C t * ‖direction‖ := by
  intro C
  have hC : 0 ≤ C := by
    have hp := actualFastChartTransferPrefix_nonneg T hT j
    have hc := actualSecondaryForcedWaveCost_nonneg m N n length j Mg CH hMg hCH
    unfold C actualConstructedSecondaryWaveBudget
    positivity
  refine ⟨hC,actualProbeSecondaryModulus_nonneg hC,actualProbeSecondaryModulus_tendsto C,?_⟩
  intro F hF t ht ht1 W hW data obs hTC hLC hRC z hz direction
  have he : obs.cost length = C := obs.cost_eq_of_profiles length L R T hTC hLC hRC
  have hout := obs.native_paper_responses F hF t ht ht1 Mg CH W data length hj hbudget hMg hCH hW z hz direction
  rw [he] at hout
  refine ⟨hout.1,?_,hout.2⟩
  obtain ⟨hell,hell1,htau,htaul⟩ := probe_original_scale_conditions t ht ht1
  have hm := obs.native_first_response (t^((6 : ℝ)/5)) length (by omega) hbudget
    hell hell1 htau htaul hMg hCH hW z hz
  rw [he] at hm
  have hscale : C*(t^(10 : ℕ))^2/(t^((6 : ℝ)/5))^2 =
      t^(10 : ℕ)*actualProbeSecondaryModulus C t := by
    have hx : C*(t^(10 : ℕ))^2/(t^((6 : ℝ)/5))^2 =
        t^(10 : ℕ)*(C*(t^(10 : ℕ)/(t^((6 : ℝ)/5))^2)) := by ring
    rw [hx,probe_delta_div_tau_sq_eq_C3_scale t ht]
    simp only [actualProbeSecondaryModulus,abs_of_pos ht]
  rw [hscale] at hm
  exact (ContinuousLinearMap.le_opNorm _ direction).trans
    (mul_le_mul_of_nonneg_right hm (norm_nonneg direction))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.native_first_response
#print axioms GlobalEmbedding.Continuation.actual_secondary_native_paper_responses_uniform
