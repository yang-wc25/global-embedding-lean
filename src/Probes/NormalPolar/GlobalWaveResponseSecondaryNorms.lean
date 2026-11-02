import NormalPolar.GlobalWaveResponseLocalNorms
import NormalPolar.ActualProbeSecondaryUniform

/-! The complete signed secondary physical array is a single joint family.
Its actual parameter is part of the observer map; primitive observation
records produce the sharp C1/C2 responses in the original atlas. There is
no pointwise choice of a completed secondary correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {m N n j r : ℕ} {Ep M Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => ProbeParameters r
private local instance secondaryNormHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance secondaryNormHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance secondaryNormHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem globalWave_secondary_native_original_norms
    (length L R : ℕ) (T : ℕ → ℝ) (Mg CH : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (hj : 3 ≤ j) (hbudget : j+1+length ≤ n)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (W : Set (Ep × M)) (hW : IsOpen W)
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j (t^((11:ℝ)/10)) Mg CH (t^(10:ℕ)) W)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (parameter : Params → Ep) (U : Set Params) (hU : IsOpen U)
    (obs : ∀ i : Fin A.count, ActualSecondaryProbeObservation F hF data (Params × D))
    (hKappa : ∀ i, (obs i).kappa = fun z => (parameter z.1,(A.chart i).symm z.2))
    (hDomain : ∀ i, U ×ˢ (A.chart i).target ⊆ (obs i).domain)
    (hSample : ∀ i u, u ∈ U → ∀ x, x ∈ A.support i → (u,A.chart i x) ∈ (obs i).sample)
    (hProfile : ∀ i, (obs i).transitionCost = T ∧ (obs i).primaryCount = L ∧ (obs i).secondaryCount = R)
    (u direction : Params) (hu : u ∈ U) :
    let S := fun v x => actualConstructedSecondarySum F hF (fun rec a => (data rec a).base)
      (t^((6:ℝ)/5)) length (parameter v,x)
    let C := actualConstructedSecondaryWaveBudget m N n j length L R Mg CH T
    let eta := actualProbeSecondaryModulus C t
    probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => S v x) u direction) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*eta*t^(10:ℕ)*‖direction‖) ∧
    probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => S v x) u direction) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*eta*t^((44:ℝ)/5)*‖direction‖) := by
  intro S C eta
  have hscaled := actual_secondary_native_paper_responses_uniform (m:=m) (N:=N) (n:=n) (j:=j)
    (U:=Params) (E:=D) (Ep:=Ep) (M:=M) (Label:=Label) (Sub:=Sub)
    length L R T Mg CH hT hMg hCH hj hbudget
  have hC := hscaled.1
  have heta : 0 ≤ eta := hscaled.2.1 t
  have he (i : Fin A.count) : (obs i).wave (t^((6:ℝ)/5)) length =
      (fun z : Params×D => S z.1 ((A.chart i).symm z.2)) := by
    funext z
    simp only [ActualSecondaryProbeObservation.wave,Function.comp_apply,hKappa i]
    rfl
  have hs (i : Fin A.count) : ContDiffOn ℝ ∞
      (fun z : Params×D => S z.1 ((A.chart i).symm z.2)) (U ×ˢ (A.chart i).target) := by
    rw [← he i]
    exact ((obs i).wave_smooth (t^((6:ℝ)/5)) length hW).mono (hDomain i)
  have hb (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :=
    hscaled.2.2.2 F hF t ht ht1 W hW data (obs i)
      (hProfile i).1 (hProfile i).2.1 (hProfile i).2.2 (u,A.chart i x) (hSample i u hu x hx)
  have h0 (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖fderiv ℝ (fun v => S v x) u‖ ≤ eta*t^(10:ℕ)*t^((6:ℝ)/5) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro d
    have hh := (hb i x hx d).1
    rw [he i] at hh
    simp only [(A.chart i).left_inv (hA.support_subset i hx)] at hh
    exact hh.trans_eq (by rw [← probe_delta_mul_tau_eq_value_scale t ht]; ring)
  have h1 (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖fderiv ℝ (fun v => fderiv ℝ (S v ∘ (A.chart i).symm) (A.chart i x)) u‖ ≤ eta*t^(10:ℕ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro d
    have hh := (hb i x hx d).2.1
    rw [he i] at hh
    exact hh.trans_eq (by ring)
  have h2 (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (S v ∘ (A.chart i).symm)) (A.chart i x)) u‖ ≤
        eta*t^(10:ℕ)/t^((6:ℝ)/5) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro d
    have hh := (hb i x hx d).2.2
    rw [he i] at hh
    exact hh.trans_eq (by rw [← probe_delta_div_tau_eq_sigma t ht]; ring)
  have hscl := probe_original_scale_conditions t ht ht1
  have hn := globalWave_original_parameter_norms_from_charts A hA U hU S hs u direction hu
    (t^((6:ℝ)/5)) (t^(10:ℕ)) eta hscl.2.2.1 (hscl.2.2.2.trans hscl.2.1)
    (pow_nonneg ht.le _) heta h0 h1 h2
  refine ⟨hn.1,?_⟩
  exact hn.2.trans_eq (congrArg ENNReal.ofReal (by
    rw [← probe_delta_div_tau_eq_sigma t ht]
    ring))

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_secondary_native_original_norms
