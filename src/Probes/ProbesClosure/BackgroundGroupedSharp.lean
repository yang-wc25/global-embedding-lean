import ProbesClosure.BackgroundCanonicalSharp
import NormalPolar.JointMixedGroupedDifferenceGerm
import NormalPolar.JointBackgroundGroupedPrescribedGerm
import NormalPolar.PassiveGroupedPrescribed

/-!
# Original grouped primitive data produces the complete sharp background response

This is the missing production-side connection between the two canonical
background inputs and their actual derivatives.  The fixed and moving forcing
germs are manufactured from the same raw grouped pieces.  Their complete
within-label cross terms, original label space, initialized ball and original
samples are preserved.  No forcing estimate, pair raw record, jointness or
finished response is assumed.  Only primitive source profiles and the existing
canonical reserve supplier remain as inputs.  Its application to the top-level
original geometry is a separate remaining integration obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
universe uM uP uS uTr uL uB uSub
variable {m N p r : ℕ} {M : Type uM} {P : Type uP} {S : Type uS}
  {Tr : Type uTr} {Λ : Type uL} {Β : Type uB}
  [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
  {Sub : Fin r → Type uSub} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => Fin p → ℝ
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual mixed grouped source manufactures both forcing germs and the
sharp native parameter derivatives of one and the same background wave.
The cost and threshold precede every scale and contracted reference map. -/
theorem probes_background_sharp_of_original_grouped_raw
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (B : BufferedAtlas P Ep)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+p) → ℝ))
    (hSamples : ∀ i, IsCompact (Samples i))
    (hDomain : ∀ i, Samples i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (rho : ℝ) (hrho : 0 < rho) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ j R, 0 ≤ Bnd j R) (hMg : ∀ j, 0 ≤ Mg j)
    (hDinput : ∀ j, 0 ≤ Dinput j) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (Tp : ℕ → ℕ → ℝ) (hTp : ∀ j k, 0 ≤ Tp j k)
    (weight : Fin r → ℝ) (Mgp Bchi Bnu Mphase Ku : ℕ → ℝ)
    (hMgp : ∀ j, 0 ≤ Mgp j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (hKu : ∀ j, 0 ≤ Ku j) (HBound : ℕ → ℝ)
    (amplitude : ℝ) (ha : 0 < amplitude) (hKu0 : Ku 0 = amplitude)
    (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
    (hsmall : jointGroupedPrescribedZeroSourceCost Sub m N p p (q+4) (q+2) (Tp 0) weight
      (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)*amplitude^2 ≤ rho/4)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    let Cp := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) p).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p (j+(q+4)) (q+2) j (Tp j) weight
        (Mgp j) (Bchi j) (Bnu j) (Mphase j) 1
    let MovingB := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) p).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p (j+(q+4)) (q+2) j (Tp j) weight
        (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
    let Cmean := round3ParameterMeanSizeCost.{uM,uTr,uP,uL,uB}
      (m := m) (d := p) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let cap := min (round4ParameterProbeForcedCap HBound rho (fun j => Cp j*amplitude^2) Cmean q (q+4))
      (round4ParameterProbeForcedCap HBound rho MovingB Cmean q (q+4))
    0 < cap ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart Samples univ),
    (∀ j, parameterRound2_originalTensorGermSeminorm A B.chart Samples univ
      hSamples hDomain ell j H ≤ HBound j) → ∀
      (s₀ : S) (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x)),
    H.val = (fun _ : P => target s₀) → ∀ (primary : Λ → Set (P × M)),
    let Fp := fun _ : P => F s₀
    let hFp := fun _ : P => hF s₀
    let gp := passiveParameterPrimary (P := P) s₀ F g
    let pj := parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell
    let ball := Metric.ball (0 : Params) (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))
    let globalU := passiveOriginalSmallParameter B amplitude ha b p₀
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart Samples univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T Fp hFp gp primary ell → ∀
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Sub l → S → D → M)
      (chi : (l : Fin r) → Sub l → S × D → ℝ)
      (nu : (l : Fin r) → (a : Sub l) → (s : S) → (x : D) →
        normalSpace (I := IM) (F s) (c l a s x))
      (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (S × M) (S × D))
      (phase : Fin r → S × M → ℝ),
    let cp := fun l k (_ : P) => c l k s₀
    let chip := fun l k (z : P × D) => chi l k (s₀,z.2)
    let nup := fun l k (_ : P) => nu l k s₀
    let ap := fun l k => passiveParameterChart (P := P) s₀ (a l k)
    let phasep := fun l (z : P × M) => phase l (s₀,z.2)
    ∀ (Omega : ℕ → Fin A.count × Fin B.count → Set (Ep × D))
      (hOmega : ∀ j i, IsOpen (Omega j i))
      (hOmegaSub : ∀ j i, Omega j i ⊆ (B.chart i.2).target ×ˢ (A.chart i.1).target)
      (hSampleOpen : ∀ j i, (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples i ⊆ Omega j i)
      (profiles : ∀ j i, JointGroupedPrescribedParameterChartRawData Fp hFp cp chip nup phasep ap
        (B.chart i.2) (A.chart i.1) (Omega j i) ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples i)
        (j+(q+4)) j ell (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Tp j))
      (huSmooth : ∀ j i, ContDiffOn ℝ ∞ (fun z : Ep × D => globalU ((B.chart i.2).symm z.1)) (Omega j i))
      (huJets : ∀ j i k, k ≤ j → ∀ z : Ep × D,
        parameterTensorModelEquiv (m+1) p z ∈ Samples i →
        ell^k*‖iteratedFDeriv ℝ k (fun z : Ep × D => globalU ((B.chart i.2).symm z.1)) z‖ ≤ Ku j)
      (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ), 0 < delta →
    (∀ i : Fin A.count, ActualOriginalPrimaryPhysicalGeometry
      (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
      (round3ParameterNativePrimary Fp gp (B.chart b))) →
    let vf := fun l k s x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l k (s,x) • nu l k s x)
    let probe := jointGroupedParameterPrescribedMean label F hF c vf phase (epsilon*ell) (q+2) a
    ∀ i : Fin A.count,
    let f := fun v x => jointMixedSeedBackgroundWave s₀ F hF g (q+2) (epsilon*ell)
      delta target probe (q+1) v ((A.chart i).symm x)
    ContDiffOn ℝ ∞ (fun z : Params × D => f z.1 z.2) (ball ×ˢ (A.chart i).target) ∧
    ∀ u ∈ ball, ∀ y ∈ (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b),
    (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
      ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ C*(epsilon*ell)*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (f v) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ C*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤ C/(epsilon*ell)*‖u‖) := by
  intro Cp MovingB Cmean cap
  let Rpair := round4ParameterProbeForcedProfile HBound (fun j => Cp j*amplitude^2) Cmean (q+4)
  let Diff := round4ParameterProbeForcedDifferenceCost Cp
    (fun j R => Cmean j R*Dinput j) Rpair (q+4)
  let Dpair := Dinput 2*Diff (q+1) (2+(q+4))
  obtain ⟨hcap,Cwave,hCwave,hSharp⟩ := probes_background_sharp_of_canonical_forcing
    (S := S) (Tr := Tr) (Λ := Λ) (Β := Β) (N := N)
    A hA B Samples hSamples hDomain rho hrho q Rsub Lprimary hq reserve hc
    Bnd Mg Dinput hBnd hMg hDinput T hT HBound (fun j => Cp j*amplitude^2) Cp MovingB
    (q+1) le_rfl
  have hDpair : 0 ≤ Dpair := mul_nonneg (hDinput 2)
    (round4ParameterProbeForcedDifferenceCost_nonneg Cp
      (fun j R => Cmean j R*Dinput j) Rpair (q+4) (q+1) (2+(q+4)))
  refine ⟨hcap,2*(Cwave*Dpair),by positivity,?_⟩
  intro ell hell hell1 H hH s₀ F hF g target hHvalue primary Fp hFp gp pj ball globalU
    supply label c chi nu a phase cp chip nup ap phasep Omega hOmega hOmegaSub hSampleOpen
    profiles huSmooth huJets epsilon he hecap delta hdelta geom vf probe i f
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le.trans (min_le_left _ _)
  have htaul : epsilon*ell ≤ ell := by nlinarith
  have hap : ∀ l k, Round3ParameterChartPreserves (ap l k) := fun _ _ => passiveParameterChart_preserves _ _
  obtain ⟨forcing,hfv,hfB,hfD⟩ := jointMixed_grouped_original_forcing_pair_from_raw
    A B.chart hA Samples hSamples hDomain (fun j => j+(q+4)) (q+2) (by intro j; omega)
    Tp hTp weight Mgp Bchi Bnu Mphase hMgp hBchi hBnu hMphase label Fp hFp cp chip nup ap hap phasep
    (epsilon*ell) ell delta (mul_pos he hell) htaul hell1 hdelta Omega hOmega hOmegaSub hSampleOpen profiles
  have hsmallMoving : jointGroupedPrescribedZeroSourceCost Sub m N p p (0+(q+4)) (q+2) (Tp 0) weight
      (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)*(Ku 0)^2 ≤ rho/4 := by
    simpa only [zero_add,hKu0] using hsmall
  obtain ⟨movingProbe,movingForce,hmv,_,hmfv,_,hmB,hmReserve⟩ :=
    jointBackground_grouped_actual_prescribed_all_order_germ A B.chart hA Samples hSamples hDomain
      (fun j => j+(q+4)) (q+2) (by intro j; omega) Tp hTp weight Mgp Bchi Bnu Mphase Ku
      hMgp hBchi hBnu hMphase hKu rho hsmallMoving label Fp hFp cp chip nup ap hap phasep
      (epsilon*ell) ell delta (mul_pos he hell) htaul hell1 hdelta Omega hOmega hOmegaSub hSampleOpen
      profiles globalU huSmooth huJets
  have hmean (v : Params) : jointGroupedParameterPrescribedMean label Fp hFp cp
      (fun l k z x => (-(delta*(epsilon*ell))/(weight l)^2) • (chip l k (z,x) • nup l k z x))
      phasep (epsilon*ell) (q+2) ap v = (fun _ : P => probe v s₀) := by
    funext z x
    exact passiveGroupedPrescribed_mean s₀ label F hF c vf phase (epsilon*ell) (q+2) a v z x
  have hfv' (v : Params) (_hv : v ∈ ball) : (forcing v).val = (delta^2)⁻¹ • (fun _ : P => probe v s₀) := by
    exact (hfv v).trans (congrArg (fun Q => (delta^2)⁻¹ • Q) (hmean v))
  have hfBound (v : Params) (hv : v ∈ ball) (j : ℕ) : pj j (forcing v) ≤ Cp j*amplitude^2 := by
    have hamplitude := jointMixed_original_ball_amplitude_bound B amplitude ha hbuffer b p₀ hp₀ v hv
    have hCp : 0 ≤ Cp j := mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ j))
      (jointGroupedPrescribedMeanUniformCost_nonneg Sub m N p (j+(q+4)) (q+2) j (Tp j)
        weight (Mgp j) (Bchi j) (Bnu j) (Mphase j) 1)
    exact (hfB j v).trans (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg v]) hCp)
  have hfReserve (v : Params) (hv : v ∈ ball) : pj 0 (forcing v) ≤ rho/4 := by
    apply (hfBound v hv 0).trans
    simpa only [Cp,Nat.cast_zero,zero_add,one_mul,jointGroupedPrescribedZeroSourceCost] using hsmall
  have hfDiff (v : Params) (_hv : v ∈ ball) (w : Params) (_hw : w ∈ ball) (j : ℕ) : pj j (forcing v-forcing w) ≤ ((‖v‖+‖w‖)*‖v-w‖)*Cp j :=
    (hfD j v w).trans_eq (by ring)
  have hmv' : movingForce.val = (delta^2)⁻¹ • (fun z : P => probe (globalU z) s₀) := by
    apply hmfv.trans
    congr 1
    funext z x
    exact congrFun (congrFun (hmean (globalU z)) z) x
  have result := hSharp ell hell hell1 H hH s₀ F hF g target probe hHvalue amplitude ha hbuffer b p₀ hp₀
    primary supply epsilon he hecap delta hdelta.ne' forcing movingForce hfv' hfBound hfReserve hfDiff
    hmv' hmB hmReserve geom i
  refine ⟨result.1,?_⟩
  intro u hu y hy
  have response := result.2 u hu y hy
  exact ⟨⟨response.1.1,response.1.2.trans_eq (by ring)⟩,
    response.2.1,⟨response.2.2.1,response.2.2.2.trans_eq (by ring)⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_background_sharp_of_original_grouped_raw
