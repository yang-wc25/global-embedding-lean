import NormalPolar.ActualProbeInitialSupplyCarrierMap
import NormalPolar.ActualProbeInitialSupplyGroupedMeanNative
import NormalPolar.ActualProbeInitialSupplyGroupedMean
import NormalPolar.ActualProbeInitialSupplyTensor

/-!
# The same complete first increment produces its original remainder germ

The native raw remainder is pulled back to the original parameter manifold,
using the same literal primary and all signed secondary sources as the map
estimate. Its opposite mean is identified with the original physical mean
before differentiating. The returned symmetric germ retains the original
charts, samples and Pi tensor norm. No completed error estimate or closed
repair state is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {M P Tr Λ Β Sub : Type*} {m d N p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance initialRestTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance initialRestTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance initialRestTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

private theorem actualProbeInitialSupply_finite_error_mean
    (F U : X → V) (Mean : X → Tensor) (delta : ℝ) (z : X) :
    actualFiniteMetricError F U Mean 1 z =
      actualFiniteMetricError F U (fun _ => 0) delta z-Mean z := by
  simp only [actualFiniteMetricError,one_pow,one_smul,smul_zero,sub_zero]

attribute [local irreducible] OpenPartialHomeomorph.symm
set_option backward.isDefEq.respectTransparency true in
theorem actualProbeInitialSupply_carrier_original_remainder_from_raw
    (nInput nSolve q probeLength j length Rbackground L Rprobe Rsecondary : ℕ)
    (hq : 1 ≤ q) (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput)
    (hprobeOrder : nSolve+2+probeLength ≤ nInput) (hbudget : j+3+length ≤ nSolve)
    (hql : q ≤ length) (hlengthBackground : length ≤ q+2) (hlengthProbe : length ≤ probeLength)
    (hLcard : Fintype.card (Λ ⊕ Fin r) ≤ L)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (hweight : ∀ l, weight l ≠ 0) (Tbackground Tprobe Tinv Tobs : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (B : Fin count → OpenPartialHomeomorph P Ep)
      (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Pieces l → P → D → M) (chi : (l : Fin r) → Pieces l → P × D → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
      (phase : Fin r → P × M → ℝ)
      (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
      (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (u : P → Fin p → ℝ) (W : Set (P × M)) (primaryDomain : Λ → Set (P × M))
      (K : (Λ ⊕ Fin r) → Set (P × M))
      (pieceK : (l : Fin r) → Pieces l → Set (P × M))
      (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ rec b, Round3ParameterChartPreserves (choice rec b).chart)
      (tau ell delta Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (raw : ActualProbeInitialCarrierRawAtlas (Tr := Tr) A B S F hF g c chi nu phase a
        input inputbar u W primaryDomain K pieceK choice nInput nSolve q probeLength j Rbackground L Rprobe Rsecondary
        reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta Tbackground Tprobe Tinv Tobs),
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let U := actualProbeInitialGroupedIncrement F hF g label c vf phase tau delta (q+2) probeLength
      length a input u choice hc
    let physicalMean := actualProbeInitialGroupedMean F hF g label c vf phase
      tau delta (q+2) probeLength a input u
    ∃ Rest : parameterRound2_originalTensorGermSpace A B S univ,
      Rest.val = incrementsOriginalMetricError (fun z => F z.1 z.2) U physicalMean 1 ∧
      parameterRound2_originalTensorGermSeminorm A B S univ hS hSO tau j Rest ≤
        C*(delta*(tau/ell)^q+delta^3/tau) := by
  obtain ⟨Cnative,hCnative,hconstruct⟩ := actualProbeInitialSupply_carrier_native_remainder_from_raw_uniform
    (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
    nInput nSolve q probeLength (j+1) length Rbackground L Rprobe Rsecondary hq hbackgroundOrder hprobeOrder
    (by omega) hql hlengthBackground hlengthProbe hLcard reserve Bnd Mg Kcut Bchi Bnu Ku Mphase
    hreserve hBnd hMg hKcut hBchi hBnu hKu hMphase weight hweight
    Tbackground Tprobe Tinv Tobs hTbackground hTprobe hTinv hTobs
  let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*Cnative
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) hCnative
  refine ⟨C,hC,?_⟩
  intro A hA B S hS hSO F hF g hg label c chi nu phase a ha input inputbar u W primaryDomain K pieceK choice hc
    tau ell delta Delta htau htaul hell1 hdelta hdeltatau raw vf U physicalMean
  let nativeAmplitude := fun (i : Fin A.count × Fin count) (imag : Bool) => jointGroupedCombinedAmplitude
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2)) label
    (fun l s t => c l s ((B i.2).symm t)) (fun l s t => vf l s ((B i.2).symm t))
    tau delta (q+2) probeLength (fun l s => round3ParameterChartPullback (B i.2) (a l s))
    (fun t => input ((B i.2).symm t)) (fun t => u ((B i.2).symm t)) imag
  let nativeSource := fun (i : Fin A.count × Fin count) (rec : Rec) (b : Sub) => jointSecondarySourceOfRawGeometry
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    nSolve (j+2) ell Mg (round3ParameterNativeDomain (B i.2) W)
    ((raw.profiles i).geometry rec b) ((raw.profiles i).host rec b) ((raw.profiles i).cutoff rec b)
    (Sum.elim (round3ParameterNativePrimary F g (B i.2)).phase
      (fun l z => phase l ((B i.2).symm z.1,z.2)))
    (nativeAmplitude i false) (nativeAmplitude i true) tau rec.val
  let nativeU := fun (i : Fin A.count × Fin count) (z : X) =>
    jointGroupedCombinedPrimary
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) label
      (fun l s t => c l s ((B i.2).symm t)) (fun l s t => vf l s ((B i.2).symm t))
      (fun l z => phase l ((B i.2).symm z.1,z.2)) tau delta (q+2) probeLength
      (fun l s => round3ParameterChartPullback (B i.2) (a l s))
      (fun t => input ((B i.2).symm t)) (u ((B i.2).symm z.1)) (z.1,(A.chart i.1).symm z.2) +
    actualParameterSecondarySourceSum
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t)) (nativeSource i)
      tau length (z.1,(A.chart i.1).symm z.2)
  let nativeMean := fun (i : Fin A.count × Fin count) => actualPrimaryOppositeMeanTensor
    (fun l t x => (Sum.elim (round3ParameterNativePrimary F g (B i.2)).phase
      (fun l z => phase l ((B i.2).symm z.1,z.2))) l (t,(A.chart i.1).symm x)) tau
    (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ))
    (fun l t (_ : Unit) x => nativeAmplitude i false l (t,(A.chart i.1).symm x))
    (fun l t (_ : Unit) x => nativeAmplitude i true l (t,(A.chart i.1).symm x))
  let nativeRest := fun (i : Fin A.count × Fin count) (z : X) =>
    actualFiniteMetricError (fun y => F ((B i.2).symm y.1) ((A.chart i.1).symm y.2))
      (nativeU i) (fun _ => 0) delta z-nativeMean i z
  have hNative (i : Fin A.count × Fin count) : ContDiffOn ℝ ∞ (nativeRest i) (raw.primary.domain i) ∧
      ∀ k ≤ j+1, ∀ z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i,
        tau^k*‖iteratedFDeriv ℝ k (nativeRest i) z‖ ≤ Cnative*(delta*(tau/ell)^q+delta^3/tau) := by
    exact hconstruct (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) label
      (fun l s t => c l s ((B i.2).symm t)) (fun l s z => chi l s ((B i.2).symm z.1,z.2))
      (fun l s t => nu l s ((B i.2).symm t)) (fun l s => round3ParameterChartPullback (B i.2) (a l s))
      (fun l z => phase l ((B i.2).symm z.1,z.2))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      (fun t => u ((B i.2).symm t)) tau ell delta Delta hdelta hdeltatau
      (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (primaryDomain l))
      (fun l => round3ParameterNativeDomain (B i.2) (K l))
      (fun l s => round3ParameterNativeDomain (B i.2) (pieceK l s))
      (raw.profiles i) (A.chart i.1) (raw.primary.domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      (raw.observer i) (raw.primary.background i) (raw.background_geometry i) (raw.primary.prescribed i)
      (raw.prescribed_geometry i) (raw.primary.piece_overlap i) (raw.primary.parameter_smooth i) (raw.primary.parameter_jets i)
  have hDomain (i) : raw.primary.domain i ⊆ (B i.2).target ×ˢ (A.chart i.1).target := by
    intro z hz
    exact ⟨((raw.primary.background i).hmapWO hz).1,raw.primary.target i z hz⟩
  have hUeq (i) : EqOn (actualRepairModelFirstDefectObservedMap A B U i) (nativeU i) (raw.primary.domain i) := by
    intro z hz
    have hh := (actualProbeInitialSupply_grouped_combined_source_pullback F hF g label c vf phase tau delta
      (q+2) probeLength length a input u (B i.2) hg ha choice hc nSolve (j+2) ell Mg
      (round3ParameterNativeDomain (B i.2) W) (raw.profiles i).geometry (raw.profiles i).host
      (raw.profiles i).cutoff (raw.choice_eq i)).1 z.1 (hDomain i hz).1 ((A.chart i.1).symm z.2)
    exact hh.symm
  have hMeq (i) : EqOn (actualOriginalNativeTargetTensor A B physicalMean i) (nativeMean i) (raw.primary.domain i) := by
    intro z hz
    exact actualProbeInitialSupply_grouped_mean_native F hF g label c vf phase tau delta
      (q+2) probeLength a input u A hA B hg ha i z (hDomain i hz)
  let Rest := incrementsOriginalMetricError (fun z => F z.1 z.2) U physicalMean 1
  have heq (i) : EqOn (actualOriginalNativeTargetTensor A B Rest i) (nativeRest i) (raw.primary.domain i) := by
    have hh := actualProbeInitialSupply_metric_error_pullback_on A B hA (fun z => F z.1 z.2) U
      physicalMean 1 i (raw.primary.domain i) (raw.primary.background i).hO (hDomain i)
      (fun y => F ((B i.2).symm y.1) ((A.chart i.1).symm y.2)) (nativeU i) (nativeMean i)
      (fun _ _ => rfl) (hUeq i) (hMeq i)
    intro z hz
    exact (hh hz).trans (actualProbeInitialSupply_finite_error_mean
      (fun y => F ((B i.2).symm y.1) ((A.chart i.1).symm y.2))
      (nativeU i) (nativeMean i) delta z)
  have hSmooth (i) : ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B Rest i) (raw.primary.domain i) :=
    (hNative i).1.congr (heq i)
  have hJets : ∀ i, ∀ k ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Rest i) z‖ ≤
        Cnative*(delta*(tau/ell)^q+delta^3/tau) := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((raw.primary.background i).hO.mem_nhds
      ((raw.primary.background i).hSO hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hNative i).2 k (by omega) z hz
  have hell : 0 < ell := htau.trans_le htaul
  have hNonneg : 0 ≤ Cnative*(delta*(tau/ell)^q+delta^3/tau) := by positivity
  have hout := actualProbeInitialSupply_tensor_original_norm_from_native A B S raw.primary.domain
    (fun i => (raw.primary.background i).hO) hDomain (fun i => (raw.primary.background i).hSO)
    Rest j tau (Cnative*(delta*(tau/ell)^q+delta^3/tau)) htau (htaul.trans hell1) hNonneg hSmooth hJets
  have hMeanSymm (b : P) (x : M) : (physicalMean b x).IsSymm :=
    actualProbeInitialGroupedMean_isSymm F hF g label c vf phase tau delta (q+2) probeLength a input u b x
  have hRestSymm (b : P) (x : M) : (Rest b x).IsSymm :=
    ((inducedMetric_isPosSemidef (I := IM) (fun y => F b y+U (b,y)) x).isSymm.sub
      (inducedMetric_isPosSemidef (I := IM) (F b) x).isSymm).sub ((hMeanSymm b x).smul (1^2))
  let E : parameterRound2_originalTensorGermSpace A B S univ := ⟨Rest,⟨by
    intro i
    refine ⟨(parameterTensorModelEquiv (m+1) d).symm ⁻¹' raw.primary.domain i,
      (raw.primary.background i).hO.preimage (parameterTensorModelEquiv (m+1) d).symm.continuous,?_,hout.1 i⟩
    intro z hz
    apply (raw.primary.background i).hSO
    simpa only [Set.mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hz,
    fun z _ => hRestSymm z.1 z.2⟩⟩
  refine ⟨E,rfl,?_⟩
  exact hout.2.2.trans_eq (by dsimp only [C]; ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_original_remainder_from_raw
