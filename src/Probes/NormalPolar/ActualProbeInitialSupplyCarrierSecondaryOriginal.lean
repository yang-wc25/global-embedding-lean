import NormalPolar.ActualProbeInitialSupplyCarrierSecondary
import NormalPolar.ActualProbeInitialSupplyCarrierAtlas
import NormalPolar.ActualProbeInitialSupplyGroupedIncrement
import NormalPolar.ActualRepairParameterBall
import NormalPolar.ActualRepairSamplingAtlas
import NormalPolar.GlobalWaveResponseLocalNorms

/-! The same actual grouped secondary on the entire original parameter ball.
The affine coordinate map lands in the original Q; each spatial observation
is identified with the same physical padded source before any derivative.
The original spatial sampling C1/C2 gauges retain their exact chart models. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m d N p r : ℕ} {M P Tr Λ Β Sub : Type*}
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Params" => Fin d → ℝ
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem actualProbeInitialSupply_carrier_secondary_original_responses
    (nInput nSolve q probeLength j length Rbackground L Rprobe Rsecondary : ℕ)
    (hq : 1 ≤ q) (hj : 1 ≤ j) (hbudget : j+3+length ≤ nSolve)
    (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput)
    (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tinv Tobs : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ t, 0 ≤ actualProbeSecondaryModulus C t) ∧
      Tendsto (actualProbeSecondaryModulus C) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (B : BufferedAtlas P Ep)
      (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
      (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
      (hQ : ∀ i, Q i ⊆ (B.chart i).target)
      (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
      (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Pieces l → P → D → M)
      (chi : (l : Fin r) → Pieces l → P × D → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
      (phase : Fin r → P × M → ℝ)
      (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
      (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (u : P → Fin p → ℝ) (primaryDomain : Λ → Set (P × M))
      (K : (Λ ⊕ Fin r) → Set (P × M))
      (pieceK : (l : Fin r) → Pieces l → Set (P × M))
      (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ rec s, Round3ParameterChartPreserves (choice rec s).chart)
      (t Delta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
      (raw : ActualProbeInitialCarrierRawAtlas (Tr := Tr) A B.chart
        (incrementsOriginalEvaluation A B.chart Omega Q univ) F hF g c chi nu phase a
        input inputbar u univ primaryDomain K pieceK choice nInput nSolve q probeLength j
        Rbackground L Rprobe Rsecondary reserve Bnd Mg Kcut Bchi Bnu Ku Mphase
        (t^((6:ℝ)/5)) (t^((11:ℝ)/10)) (t^(10:ℕ)) Delta Tbackground Tprobe Tinv Tobs),
    let tau := t^((6:ℝ)/5)
    let delta := t^(10:ℕ)
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let source := actualProbeInitialGroupedSource F hF g label c vf phase tau delta
      (q+2) probeLength a input u choice hc
    ∀ (b : Fin B.count) (p₀ : P), p₀ ∈ B.inner b →
    let ball := Metric.ball (0 : Params) (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))
    let S := fun v x => actualParameterSecondarySourceSum F hF source tau length
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ v,x)
    (∀ i, ContDiffOn ℝ ∞ (fun z : Params × D => S z.1 ((A.chart i).symm z.2))
      (ball ×ˢ (A.chart i).target)) ∧
    (∀ i v, v ∈ ball → ∀ y ∈ Omega i, ∀ direction : Params,
      ‖fderiv ℝ (fun w => S w ((A.chart i).symm y)) v direction‖ ≤
        t^((56:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fun x => S w ((A.chart i).symm x)) y) v direction‖ ≤
        t^(10:ℕ)*actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (fun x => S w ((A.chart i).symm x))) y) v direction‖ ≤
        t^((44:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖) ∧
    ∀ v direction : Params, v ∈ ball →
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 1
        (fun x => fderiv ℝ (fun w => S w x) v direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*actualProbeSecondaryModulus C t*t^(10:ℕ)*‖direction‖) ∧
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 2
        (fun x => fderiv ℝ (fun w => S w x) v direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*actualProbeSecondaryModulus C t*t^((44:ℝ)/5)*‖direction‖) := by
  let coordinate : (Params × D) ≃L[ℝ] X :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.prodCongr (ContinuousLinearEquiv.refl ℝ D)
  obtain ⟨C,hC,heta,hlimit,hconstruct⟩ := actualProbeInitialSupply_carrier_secondary_responses_uniform
    (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (p := p)
    (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub) (U := Params) (E := D)
    nInput nSolve q probeLength (j+1) length Rbackground L Rsecondary hq (by omega) (by omega)
    hbackgroundOrder hprobeOrder reserve Bnd Mg Kcut Bchi Bnu Ku Mphase
    hreserve hBnd hMg hKcut hBchi hBnu hKu hMphase weight Tbackground Tprobe Tinv Tobs
    hTbackground hTprobe hTinv hTobs coordinate
  refine ⟨C,hC,heta,hlimit,?_⟩
  intro A hA B Omega Q hOmega hQ hSampling F hF g hg label c chi nu phase a ha input inputbar u
    primaryDomain K pieceK choice hc t Delta ht ht1 raw tau delta vf source b p₀ hp₀ ball S
  let center : X := (B.chart b p₀,0)
  let coord : Params → Ep := fun v => B.chart b p₀+(EuclideanSpace.equiv (Fin d) ℝ).symm v
  have hcoordinate (z : Params × D) : center+coordinate z = (coord z.1,z.2) := by
    simp only [center,coordinate,ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply,Prod.mk_add_mk,zero_add,coord]
  let sample := fun i : Fin A.count => (parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation A B.chart Omega Q univ (i,b)
  have hsample (i : Fin A.count) (z : X) :
      z ∈ sample i ↔ z.1 ∈ Q b ∧ z.2 ∈ Omega i := by
    have he := (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
    rw [parameterTensorModelEquiv_symm_apply] at he
    have hp := congrArg Prod.fst he
    have hx := congrArg Prod.snd he
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 at hp
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at hx
    simp only [sample,mem_preimage,incrementsOriginalEvaluation,incrementsOriginalDifferentiation,
      hp,hx,mem_ofPred_eq,mem_univ,and_true]
    exact ⟨fun h => ⟨h.2.2,h.2.1⟩,fun h => ⟨⟨hOmega i h.2,hQ b h.1⟩,h.2,h.1⟩⟩
  have hcoord (v : Params) (hv : v ∈ ball) : coord v ∈ Q b :=
    actualRepairParameter_coordinates_mem_fixed_sample (tensorChartFamilyOfAtlas B) Q hSampling b p₀ hp₀ v
      (by simpa only [ball,Metric.mem_ball,dist_zero_right] using hv)
  let nativeAmplitude := fun (i : Fin A.count) (imag : Bool) => jointGroupedCombinedAmplitude
    (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
    (round3ParameterNativePrimary F g (B.chart b)) label
    (fun l s t => c l s ((B.chart b).symm t)) (fun l s t => vf l s ((B.chart b).symm t))
    tau delta (q+2) probeLength (fun l s => round3ParameterChartPullback (B.chart b) (a l s))
    (fun t => input ((B.chart b).symm t)) (fun t => u ((B.chart b).symm t)) imag
  let nativeSource := fun (i : Fin A.count) (rec : Rec) (s : Sub) => jointSecondarySourceOfRawGeometry
    (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
    nSolve (j+2) (t^((11:ℝ)/10)) Mg (round3ParameterNativeDomain (B.chart b) univ)
    ((raw.profiles (i,b)).geometry rec s) ((raw.profiles (i,b)).host rec s) ((raw.profiles (i,b)).cutoff rec s)
    (Sum.elim (round3ParameterNativePrimary F g (B.chart b)).phase
      (fun l z => phase l ((B.chart b).symm z.1,z.2)))
    (nativeAmplitude i false) (nativeAmplitude i true) tau rec.val
  let nativeWave := fun (i : Fin A.count) (z : Params × D) => actualParameterSecondarySourceSum
    (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t)) (nativeSource i)
    tau length (coord z.1,(A.chart i).symm z.2)
  have hNative (i : Fin A.count) := hconstruct
    (fun t => F ((B.chart b).symm t)) (fun t => hF ((B.chart b).symm t))
    (round3ParameterNativePrimary F g (B.chart b)) label
    (fun l s t => c l s ((B.chart b).symm t)) (fun l s z => chi l s ((B.chart b).symm z.1,z.2))
    (fun l s t => nu l s ((B.chart b).symm t)) (fun l s => round3ParameterChartPullback (B.chart b) (a l s))
    (fun l z => phase l ((B.chart b).symm z.1,z.2))
    (fun t => input ((B.chart b).symm t)) (fun t => inputbar ((B.chart b).symm t))
    (fun t => u ((B.chart b).symm t)) t Delta ht ht1
    (round3ParameterNativeDomain (B.chart b) univ) (raw.primary.background (i,b)).prim.hW
    (fun l => round3ParameterNativeDomain (B.chart b) (primaryDomain l))
    (fun l => round3ParameterNativeDomain (B.chart b) (K l))
    (fun l s => round3ParameterNativeDomain (B.chart b) (pieceK l s))
    (raw.profiles (i,b)) (A.chart i) (raw.primary.domain (i,b)) (sample i) (raw.observer (i,b))
    ((B.chart b).target ×ˢ (A.chart i).target) ((B.chart b).open_target.prod (A.chart i).open_target)
    (fun z hz => ⟨hQ b ((hsample i z).mp hz).1,hOmega i ((hsample i z).mp hz).2⟩)
    (fun _ hz => hz.2) (fun _ hz => ⟨hz.1,mem_univ _⟩) center
  have hEq (i : Fin A.count) (v : Params) (hv : v ∈ ball) (y : D) :
      nativeWave i (v,y) = S v ((A.chart i).symm y) := by
    have hbinding (rec : Rec) (s : Sub) : ActualProbeInitialSourcePullbackBinding
        (B.chart b) (source rec s) (nativeSource i rec s) :=
      actualProbeInitialSupply_grouped_secondary_binding F hF g label c vf phase tau delta
        (q+2) probeLength a input u (B.chart b) hg ha rec.val (choice rec s) (hc rec s)
        nSolve (j+2) (t^((11:ℝ)/10)) Mg (round3ParameterNativeDomain (B.chart b) univ)
        ((raw.profiles (i,b)).geometry rec s) ((raw.profiles (i,b)).host rec s)
        ((raw.profiles (i,b)).cutoff rec s) (raw.choice_eq (i,b) rec s)
    exact actualProbeInitialSupply_secondary_sum_pullback_of_binding F hF source (nativeSource i)
      (B.chart b) hbinding tau length (coord v) (hQ b (hcoord v hv)) ((A.chart i).symm y)
  have hSmooth (i : Fin A.count) : ContDiffOn ℝ ∞
      (fun z : Params × D => S z.1 ((A.chart i).symm z.2)) (ball ×ˢ (A.chart i).target) := by
    have hs := (hNative i).1
    simp only [hcoordinate] at hs
    change ContDiffOn ℝ ∞ (nativeWave i)
      ((fun z : Params × D => (coord z.1,z.2)) ⁻¹' ((B.chart b).target ×ˢ (A.chart i).target)) at hs
    exact (hs.mono (fun z hz => ⟨hQ b (hcoord z.1 hz.1),hz.2⟩)).congr
      (fun z hz => (hEq i z.1 hz.1 z.2).symm)
  have hResponse (i : Fin A.count) (v : Params) (hv : v ∈ ball) (y : D) (hy : y ∈ Omega i)
      (direction : Params) := by
    have hN := (hNative i).2
    simp only [hcoordinate] at hN
    exact hN (v,y) ((hsample i (coord v,y)).mpr ⟨hcoord v hv,hy⟩) direction
  have hResponseOriginal (i : Fin A.count) (v : Params) (hv : v ∈ ball) (y : D) (hy : y ∈ Omega i)
      (direction : Params) :
      ‖fderiv ℝ (fun w => S w ((A.chart i).symm y)) v direction‖ ≤
        t^((56:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fun x => S w ((A.chart i).symm x)) y) v direction‖ ≤
        t^(10:ℕ)*actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (fun x => S w ((A.chart i).symm x))) y) v direction‖ ≤
        t^((44:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖ := by
    have hb := hResponse i v hv y hy direction
    change ‖fderiv ℝ (fun w => nativeWave i (w,y)) v direction‖ ≤ _ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fun x => nativeWave i (w,x)) y) v direction‖ ≤ _ ∧
      ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (fun x => nativeWave i (w,x))) y) v direction‖ ≤ _ at hb
    have h0 : (fun w => nativeWave i (w,y)) =ᶠ[𝓝 v] (fun w => S w ((A.chart i).symm y)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
      exact hEq i w hw y
    have h1 : (fun w => fderiv ℝ (fun x => nativeWave i (w,x)) y) =ᶠ[𝓝 v]
        (fun w => fderiv ℝ (fun x => S w ((A.chart i).symm x)) y) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
      rw [show (fun x => nativeWave i (w,x)) = (fun x => S w ((A.chart i).symm x)) from funext (hEq i w hw)]
    have h2 : (fun w => fderiv ℝ (fderiv ℝ (fun x => nativeWave i (w,x))) y) =ᶠ[𝓝 v]
        (fun w => fderiv ℝ (fderiv ℝ (fun x => S w ((A.chart i).symm x))) y) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
      rw [show (fun x => nativeWave i (w,x)) = (fun x => S w ((A.chart i).symm x)) from funext (hEq i w hw)]
    rwa [h0.fderiv_eq,h1.fderiv_eq,h2.fderiv_eq] at hb
  refine ⟨hSmooth,hResponseOriginal,?_⟩
  intro v direction hv
  let As := actualRepairSamplingAtlas A Omega
  have hEta : 0 ≤ actualProbeSecondaryModulus C t := heta t
  have hAs := actualRepairSamplingAtlas_smooth A hA Omega hOmega
  have hpoint (i : Fin A.count) (x : M) (hx : x ∈ As.support i) : A.chart i x ∈ Omega i := by
    rw [← actualRepairSamplingAtlas_coordinate_support A Omega hOmega i]
    exact ⟨x,hx,rfl⟩
  have h0 (i : Fin As.count) (x : M) (hx : x ∈ As.support i) :
      ‖fderiv ℝ (fun w => S w x) v‖ ≤ actualProbeSecondaryModulus C t*t^10*t^((6:ℝ)/5) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    have hb := (hResponseOriginal i v hv (A.chart i x) (hpoint i x hx) a).1
    rw [(A.chart i).left_inv (hAs.support_subset i hx)] at hb
    exact hb.trans_eq (by rw [← probe_delta_mul_tau_eq_value_scale t ht]; ring)
  have h1 (i : Fin As.count) (x : M) (hx : x ∈ As.support i) :
      ‖fderiv ℝ (fun w => fderiv ℝ (S w ∘ (As.chart i).symm) (As.chart i x)) v‖ ≤
        actualProbeSecondaryModulus C t*t^10 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    exact ((hResponseOriginal i v hv (A.chart i x) (hpoint i x hx) a).2.1).trans_eq (by ring)
  have h2 (i : Fin As.count) (x : M) (hx : x ∈ As.support i) :
      ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (S w ∘ (As.chart i).symm)) (As.chart i x)) v‖ ≤
        actualProbeSecondaryModulus C t*t^10/t^((6:ℝ)/5) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    exact ((hResponseOriginal i v hv (A.chart i x) (hpoint i x hx) a).2.2).trans_eq
      (by rw [← probe_delta_div_tau_eq_sigma t ht]; ring)
  have hscales := probe_original_scale_conditions t ht ht1
  have hn := globalWave_original_parameter_norms_from_charts As hAs ball Metric.isOpen_ball S hSmooth
    v direction hv (t^((6:ℝ)/5)) (t^10) (actualProbeSecondaryModulus C t)
    hscales.2.2.1 (hscales.2.2.2.trans hscales.2.1) (pow_nonneg ht.le _) (heta t) h0 h1 h2
  refine ⟨hn.1,?_⟩
  exact hn.2.trans_eq (congrArg ENNReal.ofReal (by
    rw [← probe_delta_div_tau_eq_sigma t ht]
    ring))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_secondary_original_responses
