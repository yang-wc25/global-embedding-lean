import ProbesClosure.GeneralFourFields
import NormalPolar.ActualProbeParameterNormSum
import NormalPolar.GlobalWaveResponseActualFirst

/-!
# The four arbitrary-cutoff responses of one complete first map

This is the component assembly for the actual grouped construction. The
prescribed input is the four-field output of the original refined family;
the background and the complete signed secondary retain their own joint
smoothness, original atlas norms, and native value/Hessian responses.
Every derivative in the conclusion concerns the literal sum of these same
three maps and the parameter-independent reference map.

This theorem does not construct any component and does not identify an
unrelated closed-state record with that sum. Its output can be passed to
`probes_first_model_of_spatial_and_four` with the original spatial bounds
of this very map. The atlas, parameter set, radius, weights,
and scale are unchanged. No general repair target is assumed.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {n N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => ProbeParameters r

private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- One complete first map inherits the original four response fields from
its actual components. `CB` and `CS` pay the original parameter norms;
`CR` pays the background's linear-in-parameter native remainder. The full
secondary remainder is added to both moduli, including all signed modes.
The prescribed component may already contain its harmless `CP * ‖u‖`
remainder, as does the existing initialized original-family theorem. -/
theorem general_probes_first_four_of_same_components
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (weight : Fin r → ℝ)
    (U : Set Params) (hU : IsOpen U) (radius t : ℝ) (ht : 0 < t)
    (reference : M → V) (href : ContMDiff IM 𝓘(ℝ,V) ∞ reference)
    (background prescribed secondary : Params → M → V)
    (hBJ : ∀ i, ContDiffOn ℝ ∞
      (fun z : Params × D => background z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (hPJ : ∀ i, ContDiffOn ℝ ∞
      (fun z : Params × D => prescribed z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (hSJ : ∀ i, ContDiffOn ℝ ∞
      (fun z : Params × D => secondary z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (CB CP CS CR etaH etaV etaS : ℝ)
    (hCB : 0 ≤ CB) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCR : 0 ≤ CR)
    (hBN : ∀ u ∈ U, ‖u‖ < radius → ∀ direction : Params,
      probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => background v x) u direction) ≤
        ENNReal.ofReal (CB*t^(10:ℕ)*‖direction‖) ∧
      probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => background v x) u direction) ≤
        ENNReal.ofReal (CB*t^((44:ℝ)/5)*‖direction‖))
    (hPN : GeneralWaveFirstFourAt F₀ hF₀ waves A weight prescribed U
      radius t CP etaH etaV)
    (hSN : ∀ u ∈ U, ‖u‖ < radius → ∀ direction : Params,
      probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => secondary v x) u direction) ≤
        ENNReal.ofReal (CS*t^(10:ℕ)*‖direction‖) ∧
      probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => secondary v x) u direction) ≤
        ENNReal.ofReal (CS*t^((44:ℝ)/5)*‖direction‖))
    (hBR : ∀ u ∈ U, ‖u‖ < radius → ∀ i x, x ∈ A.support i →
      ∀ direction : Params,
      ‖fderiv ℝ (fun v => background v x) u direction‖ ≤
        t^((56:ℝ)/5)*(CR*‖u‖)*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (background v ∘ (A.chart i).symm))
        (A.chart i x)) u direction‖ ≤
        t^((44:ℝ)/5)*(CR*‖u‖)*‖direction‖)
    (hSR : ∀ u ∈ U, ‖u‖ < radius → ∀ i x, x ∈ A.support i →
      ∀ direction : Params,
      ‖fderiv ℝ (fun v => secondary v x) u direction‖ ≤
        t^((56:ℝ)/5)*etaS*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (secondary v ∘ (A.chart i).symm))
        (A.chart i x)) u direction‖ ≤
        t^((44:ℝ)/5)*etaS*‖direction‖) :
    let C := CB+CP+CS+CR
    let G := fun u x => reference x+background u x+prescribed u x+secondary u x
    0 ≤ C ∧ GeneralWaveFirstFourAt F₀ hF₀ waves A weight G U radius t C
      (etaH+etaS) (etaV+etaS) := by
  intro C G
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnormC : CB+CP+CS ≤ C := by dsimp [C]; linarith
  have hresponseC : CR+CP ≤ C := by dsimp [C]; linarith
  refine ⟨hC,?_⟩
  intro u hu hur
  have hP := hPN u hu hur
  have hsum (l : Fin r) (sine : Bool) (i : Fin A.count) (x : M)
      (hx : x ∈ A.support i) := by
    have hsx := hA.support_subset i hx
    have hy := (A.chart i).map_source hsx
    have hB := hBR u hu hur i x hx (Pi.single (l,sine) 1)
    have hS := hSR u hu hur i x hx (Pi.single (l,sine) 1)
    simp only [Pi.norm_single,norm_one,mul_one] at hB hS
    exact globalWave_initial_sum_response_bounds U (A.chart i).target hU (A.chart i).open_target
      (reference ∘ (A.chart i).symm)
      (fun v => background v ∘ (A.chart i).symm)
      (fun v => prescribed v ∘ (A.chart i).symm)
      (fun v => secondary v ∘ (A.chart i).symm)
      ((href.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn)
      (hBJ i) (hPJ i) (hSJ i) u (Pi.single (l,sine) 1) hu (A.chart i x) hy
      _ _ _ _ _ _ _ _
      (by simpa only [Function.comp_apply,(A.chart i).left_inv hsx] using hB.1)
      (by simpa only [Function.comp_apply,(A.chart i).left_inv hsx] using hP.2.2.2 l sine x)
      (by simpa only [Function.comp_apply,(A.chart i).left_inv hsx] using hS.1)
      hB.2 (hP.2.2.1 l sine i x hx) hS.2
  refine ⟨?_,?_,?_,?_⟩
  · intro direction
    have hn := actual_probe_first_parameter_norm_of_components A hA hcover 1 U hU
      reference background prescribed secondary hBJ hPJ hSJ u direction hu
      (by positivity) (by positivity) (by positivity)
      (hBN u hu hur direction).1 (hP.1 direction) (hSN u hu hur direction).1
    exact hn.trans (ENNReal.ofReal_le_ofReal (by
      calc
        _ = (CB+CP+CS)*t^(10:ℕ)*‖direction‖ := by ring
        _ ≤ C*t^(10:ℕ)*‖direction‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnormC (pow_nonneg ht.le _)) (norm_nonneg _)))
  · intro direction
    have hn := actual_probe_first_parameter_norm_of_components A hA hcover 2 U hU
      reference background prescribed secondary hBJ hPJ hSJ u direction hu
      (by positivity) (by positivity) (by positivity)
      (hBN u hu hur direction).2 (hP.2.1 direction) (hSN u hu hur direction).2
    exact hn.trans (ENNReal.ofReal_le_ofReal (by
      calc
        _ = (CB+CP+CS)*t^((44:ℝ)/5)*‖direction‖ := by ring
        _ ≤ C*t^((44:ℝ)/5)*‖direction‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnormC (Real.rpow_nonneg ht.le _)) (norm_nonneg _)))
  · intro l sine i x hx
    have hh := (hsum l sine i x hx).2
    exact hh.trans (by
      calc
        _ = t^((44:ℝ)/5)*((etaH+etaS)+(CR+CP)*‖u‖) := by ring
        _ ≤ t^((44:ℝ)/5)*((etaH+etaS)+C*‖u‖) :=
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_right hresponseC (norm_nonneg u)))
            (Real.rpow_nonneg ht.le _))
  · intro l sine x
    obtain ⟨i,hx⟩ := hcover x
    have hh := (hsum l sine i x hx).1
    simp only [Function.comp_apply,(A.chart i).left_inv (hA.support_subset i hx)] at hh
    exact hh.trans (by
      calc
        _ = t^((56:ℝ)/5)*((etaV+etaS)+(CR+CP)*‖u‖) := by ring
        _ ≤ t^((56:ℝ)/5)*((etaV+etaS)+C*‖u‖) :=
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_right hresponseC (norm_nonneg u)))
            (Real.rpow_nonneg ht.le _))

/-- Equality of whole spatial slices on the actual open parameter set is
enough to transport all four fields to a totalized or pulled-back map.
The equality is used on a parameter neighborhood before differentiating;
pointwise equality at a single parameter would not justify this step. -/
theorem general_probes_first_four_congr_on_open
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    (A : BufferedAtlas M D) (weight : Fin r → ℝ)
    (U : Set Params) (hU : IsOpen U)
    (G H : Params → M → V) (hEq : EqOn G H U)
    (radius t C etaH etaV : ℝ)
    (hG : GeneralWaveFirstFourAt F₀ hF₀ waves A weight G U radius t C etaH etaV) :
    GeneralWaveFirstFourAt F₀ hF₀ waves A weight H U radius t C etaH etaV := by
  intro u hu hur
  have hg := hG u hu hur
  have he : G =ᶠ[𝓝 u] H := hEq.eventuallyEq_of_mem (hU.mem_nhds hu)
  have hvalue (x : M) :
      fderiv ℝ (fun v => G v x) u = fderiv ℝ (fun v => H v x) u :=
    Filter.EventuallyEq.fderiv_eq (he.mono (fun _ hv => congrFun hv x))
  have hparameter (direction : Params) :
      (fun x => fderiv ℝ (fun v => G v x) u direction) =
      (fun x => fderiv ℝ (fun v => H v x) u direction) := by
    funext x
    rw [hvalue x]
  have hhessian (i : Fin A.count) (x : M) :
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v ∘ (A.chart i).symm))
        (A.chart i x)) u =
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (H v ∘ (A.chart i).symm))
        (A.chart i x)) u := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [he] with v hv
    rw [hv]
  refine ⟨?_,?_,?_,?_⟩
  · intro direction
    rw [← hparameter direction]
    exact hg.1 direction
  · intro direction
    rw [← hparameter direction]
    exact hg.2.1 direction
  · intro l sine i x hx
    rw [← hhessian i x]
    exact hg.2.2.1 l sine i x hx
  · intro l sine x
    rw [← hvalue x]
    exact hg.2.2.2 l sine x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.general_probes_first_four_of_same_components
#print axioms GlobalEmbedding.Continuation.general_probes_first_four_congr_on_open
