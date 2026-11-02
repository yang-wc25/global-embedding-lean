import NormalPolar.JointMixedPassiveBackgroundJoint
import NormalPolar.GlobalWaveResponseBackgroundGlobal
import NormalPolar.GlobalWaveResponseBackgroundNativeC1

/-! Sharp external-parameter value, first spatial and Hessian responses
of the same passive background. Jointness is produced from the actual
moving-parameter raw record. Two-input native profiles supply the actual
fast difference, on the unchanged original samples and full original ball. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N p : ℕ} {M S P Tr Λ Β : Type*}
  [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "X" => Ep × D
local notation "Params" => Fin p → ℝ
local notation "IM" => 𝓘(ℝ,D)
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

private theorem jointMixed_background_ignore_native_parameter
    (f : Params → D → V) (U : Set Params) (E : Set D) (O : Set X)
    (hf : ContDiffOn ℝ ∞ (fun z : Params × D => f z.1 z.2) (U ×ˢ E))
    (hOE : ∀ z ∈ O, z.2 ∈ E) :
    ContDiffOn ℝ ∞ (fun z : (Params × Ep) × D => f z.1.1 z.2)
      {z | z.1.1 ∈ U ∧ (z.1.2,z.2) ∈ O} :=
  hf.comp (contDiff_fst.fst.prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨hz.1,hOE _ hz.2⟩)

abbrev jointMixedPassiveBackgroundSharpStatement
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ) (C : ℝ) : Prop :=
    ∀
      (s₀ : S) (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (tau delta : ℝ)
      (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (probe : Params → (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (iteration : ℕ)
      (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
      (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
      (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
      (primary : Λ → Set (P × M)) (e : OpenPartialHomeomorph M D) (Samples : Set X)
      (ell DeltaSmooth Dpair : ℝ) (hDpair : 0 ≤ Dpair)
      (nSmooth jSmooth RsubSmooth LprimarySmooth : ℕ)
      (horderSmooth : jSmooth+2+length ≤ nSmooth)
      (reserveSmooth BndSmooth MgSmooth : ℝ) (hcSmooth : 0 < reserveSmooth)
      (hBndSmooth : 0 ≤ BndSmooth) (hMgSmooth : 0 ≤ MgSmooth)
      (TSmooth : ℕ → ℝ) (hTSmooth : ∀ k, 0 ≤ TSmooth k),
    let ball := Metric.ball (0 : Params) (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))
    let Fp := fun _ : P => F s₀
    let hFp := fun _ : P => hF s₀
    let gp := passiveParameterPrimary (P := P) s₀ F g
    let Fn := fun t => Fp ((B.chart b).symm t)
    let hFn := fun t => hFp ((B.chart b).symm t)
    let gn := round3ParameterNativePrimary Fp gp (B.chart b)
    let W := round3ParameterNativeDomain (B.chart b) (univ : Set (P × M))
    let Kprimary := fun l => round3ParameterNativeDomain (B.chart b) (primary l)
    let O := actualRawObserverOpen e W
    let moving := jointMixedPassiveBackgroundInput s₀ F hF g length tau delta target probe iteration
      (passiveOriginalSmallParameter B amplitude ha b p₀)
    let fixed := fun v (_ : Ep) => actualParameterBackgroundMeanIterate F hF g
      length tau delta target probe iteration v s₀
    ∀ (rawSmooth : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nSmooth length jSmooth RsubSmooth LprimarySmooth
      reserveSmooth BndSmooth MgSmooth TSmooth Fn hFn gn (fun t => moving ((B.chart b).symm t))
      (fun t => moving ((B.chart b).symm t)) W Kprimary e O Samples tau ell DeltaSmooth)
      (geom : ActualOriginalPrimaryPhysicalGeometry Fn hFn gn)
      (pairs : ∀ v ∈ ball, ∀ u ∈ ball, ∃ Delta : ℝ,
        Delta ≤ Dpair*(‖v‖+‖u‖)*‖v-u‖ ∧
        Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
          reserve Bnd Mg T Fn hFn gn (fixed v) (fixed u) W Kprimary e O Samples tau ell Delta)),
    ∀ u ∈ ball, ∀ y ∈ Samples,
    let f := fun v x => jointMixedSeedBackgroundWave s₀ F hF g length tau delta target probe iteration v (e.symm x)
    (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
      ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ 2*(C*Dpair*tau)*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (f v) y.2) (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ 2*(C*Dpair)*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤ 2*(C*Dpair/tau)*‖u‖)

theorem jointMixed_passive_background_ball_sharp_from_raw
    (n length j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n) (hj : 2 ≤ j)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ jointMixedPassiveBackgroundSharpStatement (S := S) (P := P)
      (M := M) (Tr := Tr) (Λ := Λ) (Β := Β) (m := m) (N := N) (p := p)
      n length j Rsub Lprimary reserve Bnd Mg T C := by
  obtain ⟨C,hC,hDiff⟩ := globalWave_background_global_raw_difference
    (I := IM) (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N)
    n length j Rsub Lprimary (by omega) reserve Bnd Mg hc hBnd hMg T hT
  refine ⟨C,hC,?_⟩
  unfold jointMixedPassiveBackgroundSharpStatement
  intro s₀ F hF g tau delta target probe iteration B amplitude ha hbuffer b p₀ hp₀
    primary e Samples ell DeltaSmooth Dpair hDpair
    nSmooth jSmooth RsubSmooth LprimarySmooth horderSmooth reserveSmooth BndSmooth MgSmooth
    hcSmooth hBndSmooth hMgSmooth TSmooth hTSmooth
    ball Fp hFp gp Fn hFn gn W Kprimary O moving fixed
    rawSmooth geom pairs u hu y hy f
  have hseed := jointMixed_passive_background_original_ball_joint s₀ F hF g length tau delta
    target probe iteration nSmooth jSmooth RsubSmooth LprimarySmooth horderSmooth
    reserveSmooth BndSmooth MgSmooth hcSmooth hBndSmooth hMgSmooth TSmooth hTSmooth
    B amplitude ha hbuffer b p₀ hp₀ primary e Samples ell DeltaSmooth rawSmooth geom
  let full : Params → X → V := fun v z => f v z.2
  have hJoint := jointMixed_background_ignore_native_parameter f ball e.target O hseed
    (fun z hz => hz.1.2)
  have hbind (v : Params) (t : Ep) (ht : t ∈ (B.chart b).target) (x : M) :
      incrementsGlobalPrimaryWave Fn hFn gn (fixed v) length tau (t,x) =
        jointMixedSeedBackgroundWave s₀ F hF g length tau delta target probe iteration v x := by
    have h := round3ParameterPrimary_pullback_wave Fp hFp gp (B.chart b)
      (passiveParameterPrimary_chart_preserves s₀ F g)
      (fun _ : P => actualParameterBackgroundMeanIterate F hF g length tau delta target probe iteration v s₀)
      length tau t ht x
    exact h.trans (passiveParameterPrimary_wave s₀ F hF g
      (actualParameterBackgroundMeanIterate F hF g length tau delta target probe iteration v)
      length tau ((B.chart b).symm t) x)
  have hpair : ∀ v ∈ ball, ∀ k ≤ 2,
      tau^k*‖iteratedFDeriv ℝ k (fun z => full v z-full u z) y‖ ≤
        (C*Dpair)*tau*(‖v‖+‖u‖)*‖v-u‖ := by
    intro v hv k hk
    obtain ⟨Delta,hDelta,⟨raw⟩⟩ := pairs v hv u hu
    have hn := hDiff Fn hFn gn (fixed v) (fixed u) W Kprimary e O Samples tau ell Delta raw
      (fun l a z hz => geom.adaptation l a _ (raw.hsource l a hz))
    have heq : EqOn
        (fun z : X => incrementsGlobalPrimaryWave Fn hFn gn (fixed v) length tau (z.1,e.symm z.2)-
          incrementsGlobalPrimaryWave Fn hFn gn (fixed u) length tau (z.1,e.symm z.2))
        (fun z => full v z-full u z) O := by
      intro z hz
      exact congrArg₂ Sub.sub (hbind v z.1 hz.2.1 (e.symm z.2))
        (hbind u z.1 hz.2.1 (e.symm z.2))
    rw [← ((heq.eventuallyEq_of_mem (raw.hO.mem_nhds (raw.hSO hy))).iteratedFDeriv ℝ k).eq_of_nhds]
    calc
      _ ≤ C*tau*Delta := hn.2 k (hk.trans hj) y hy
      _ ≤ C*tau*(Dpair*(‖v‖+‖u‖)*‖v-u‖) :=
        mul_le_mul_of_nonneg_left hDelta (mul_nonneg hC raw.htau.le)
      _ = _ := by ring
  have hVH := globalWave_native_background_value_hessian_of_fast_difference full ball O Metric.isOpen_ball
    rawSmooth.hO hJoint u hu y (rawSmooth.hSO hy) tau (C*Dpair) rawSmooth.htau
    (mul_nonneg hC hDpair) hpair
  have hFirst := globalWave_native_background_first_of_fast_difference full ball O Metric.isOpen_ball
    rawSmooth.hO hJoint u hu y (rawSmooth.hSO hy) tau (C*Dpair) rawSmooth.htau
    (mul_nonneg hC hDpair) hpair
  exact ⟨hVH.1,hFirst,hVH.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_passive_background_ball_sharp_from_raw
