import NormalPolar.JointMixedBackgroundBallSharp
import NormalPolar.JointMixedCanonicalPair
import NormalPolar.JointMixedForcedResidual
import NormalPolar.JointMixedGroupedBackgroundBinding
import NormalPolar.ActualProbeInitialSupplyPrimaryOriginal

/-!
# The genuine canonical background has sharp responses on its original ball

Source: the finite background substitutions in the proof of `prop:probes`,
original manuscript lines 888--904.  The two actual canonical producers are
used here together.  The moving forcing gives joint regularity, while two
fixed forcing inputs give the sharp difference estimate.  Both records are
rewritten to the literal same finite iterate before differentiation.  In
particular no pointwise selected raw witness is differentiated, and neither
joint smoothness nor a finished background response is a hypothesis.

The primitive forcing germs and their existing original-seminorm budgets are
still inputs to this integration lemma.  They are produced by the original
wave and grouped forcing modules; this file does not claim the original
unconditional probes theorem.  The source samples and the whole already
initialized parameter ball are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar

universe uM uP uS uTr uL uB
variable {m N p : ℕ} {M : Type uM} {P : Type uP} {S : Type uS}
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

/-- One constant is fixed before ell, the contracted reference map, both
forcing germs and the small scales.  The constant comes only from the actual
two-input primitive cost, not the auxiliary moving-family regularity cost. -/
theorem probes_background_sharp_of_canonical_forcing
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+p) → ℝ))
    (hSamples : ∀ i, IsCompact (Samples i))
    (hDomain : ∀ i, Samples i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ j R, 0 ≤ Bnd j R) (hMg : ∀ j, 0 ≤ Mg j)
    (hDinput : ∀ j, 0 ≤ Dinput j) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (HBound ProbeB ProbeDiff MovingB : ℕ → ℝ)
    (iteration : ℕ) (hiteration : iteration ≤ q+1) :
    let Cmean := round3ParameterMeanSizeCost.{uM,uTr,uP,uL,uB}
      (m := m) (d := p) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let Rpair := round4ParameterProbeForcedProfile HBound ProbeB Cmean (q+4)
    let Rmoving := round4ParameterProbeForcedProfile HBound MovingB Cmean (q+4)
    let Diff := round4ParameterProbeForcedDifferenceCost ProbeDiff
      (fun j R => Cmean j R*Dinput j) Rpair (q+4)
    let Dpair := Dinput 2*Diff iteration (2+(q+4))
    let cap := min (round4ParameterProbeForcedCap HBound rho ProbeB Cmean q (q+4))
      (round4ParameterProbeForcedCap HBound rho MovingB Cmean q (q+4))
    0 < cap ∧ ∃ Cwave : ℝ, 0 ≤ Cwave ∧ ∀
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart Samples univ),
    (∀ j, parameterRound2_originalTensorGermSeminorm A B.chart Samples univ
      hSamples hDomain ell j H ≤ HBound j) → ∀
      (s₀ : S) (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (probe : Params → (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x)),
    H.val = (fun _ : P => target s₀) → ∀
      (amplitude : ℝ) (ha : 0 < amplitude)
      (hbuffer : B.buffer ≤ amplitude/(‖(EuclideanSpace.equiv (Fin p) ℝ).toContinuousLinearMap‖+1))
      (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
      (primary : Λ → Set (P × M)),
    let Fp := fun _ : P => F s₀
    let hFp := fun _ : P => hF s₀
    let gp := passiveParameterPrimary (P := P) s₀ F g
    let pj := parameterRound2_originalTensorGermSeminorm A B.chart Samples univ hSamples hDomain ell
    let ball := Metric.ball (0 : Params) (actualRepairParameterRadius (tensorChartFamilyOfAtlas B))
    let globalU := passiveOriginalSmallParameter B amplitude ha b p₀
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart Samples univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T Fp hFp gp primary ell → ∀
      (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ), delta ≠ 0 → ∀
      (forcing : Params → parameterRound2_originalTensorGermSpace A B.chart Samples univ)
      (movingForce : parameterRound2_originalTensorGermSpace A B.chart Samples univ),
    (∀ u ∈ ball, (forcing u).val = (delta^2)⁻¹ • (fun _ : P => probe u s₀)) →
    (∀ u ∈ ball, ∀ j, pj j (forcing u) ≤ ProbeB j) →
    (∀ u ∈ ball, pj 0 (forcing u) ≤ rho/4) →
    (∀ u ∈ ball, ∀ v ∈ ball, ∀ j,
      pj j (forcing u-forcing v) ≤ ((‖u‖+‖v‖)*‖u-v‖)*ProbeDiff j) →
    movingForce.val = (delta^2)⁻¹ • (fun z : P => probe (globalU z) s₀) →
    (∀ j, pj j movingForce ≤ MovingB j) → pj 0 movingForce ≤ rho/4 →
    (∀ i : Fin A.count, ActualOriginalPrimaryPhysicalGeometry
      (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
      (round3ParameterNativePrimary Fp gp (B.chart b))) →
    ∀ i : Fin A.count,
    let f := fun v x => jointMixedSeedBackgroundWave s₀ F hF g (q+2) (epsilon*ell)
      delta target probe iteration v ((A.chart i).symm x)
    ContDiffOn ℝ ∞ (fun z : Params × D => f z.1 z.2) (ball ×ˢ (A.chart i).target) ∧
    ∀ u ∈ ball, ∀ y ∈ (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b),
    (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
      ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ 2*(Cwave*Dpair*(epsilon*ell))*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (f v) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ 2*(Cwave*Dpair)*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤
        2*(Cwave*Dpair/(epsilon*ell))*‖u‖) := by
  intro Cmean Rpair Rmoving Diff Dpair cap
  have hcapP := round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB Cmean q (q+4)
  have hcapM := round4ParameterProbeForcedCap_pos HBound rho hrho MovingB Cmean q (q+4)
  obtain ⟨Cwave,hCwave,hSharp⟩ := jointMixed_passive_background_ball_sharp_from_raw
    (S := S) (P := P) (M := M) (Tr := Tr) (Λ := Λ) (Β := Β) (m := m) (N := N) (p := p)
    (2+(q+4)) (q+2) 2 Rsub Lprimary (by omega) (by omega)
    reserve (Bnd 2 (Rpair iteration (2+(q+4)))) (Mg 2) hc (hBnd _ _) (hMg _ ) T hT
  refine ⟨lt_min hcapP hcapM,Cwave,hCwave,?_⟩
  intro ell hell hell1 H hH s₀ F hF g target probe hHv amplitude ha hbuffer b p₀ hp₀ primary
    Fp hFp gp pj ball globalU supply epsilon he hecap delta hdelta forcing movingForce
    hfv hfBound hfReserve hfDiff hmv hmBound hmReserve geom i f
  have heP : epsilon < round4ParameterProbeForcedCap HBound rho ProbeB Cmean q (q+4) :=
    hecap.trans_le (min_le_left _ _)
  have heM : epsilon < round4ParameterProbeForcedCap HBound rho MovingB Cmean q (q+4) :=
    hecap.trans_le (min_le_right _ _)
  obtain ⟨K,hKv,hKr,hKb,hKd,hPair⟩ :=
    (jointMixed_canonical_forced_pair_raw (Tr := Tr) (Λ := Λ) (Β := Β) (p := p) (N := N)
      A B.chart hA Samples hSamples hDomain ell hell hell1 H HBound hH rho hrho q Rsub Lprimary hq
      reserve hc Bnd Mg Dinput hBnd hMg hDinput T hT ProbeB ProbeDiff).2
      Fp hFp gp (passiveParameterPrimary_chart_preserves s₀ F g) primary supply epsilon he heP delta
      ball (fun v (_ : P) => probe v s₀) forcing hfv hfBound hfReserve hfDiff
  obtain ⟨Km,hKmv,hKmr,hKmb,hMoving,_⟩ :=
    (jointMixed_canonical_forced_mean_residual (Tr := Tr) (Λ := Λ) (Β := Β) (N := N)
      A B.chart hA Samples hSamples hDomain ell hell hell1 H HBound hH rho hrho q Rsub Lprimary hq
      reserve hc Bnd Mg Dinput hBnd hMg hDinput T hT MovingB).2
      Fp hFp gp (passiveParameterPrimary_chart_preserves s₀ F g) primary supply epsilon he heM delta
      hdelta (fun z : P => probe (globalU z) s₀) movingForce hmv hmBound hmReserve
  obtain ⟨rawMoving⟩ := hMoving iteration hiteration 2
  have hMovingValue : (Km iteration).val = jointMixedPassiveBackgroundInput
      s₀ F hF g (q+2) (epsilon*ell) delta target probe iteration globalU := by
    rw [hKmv iteration hiteration,hHv]
    rfl
  have hFixedValue (v : Params) (hv : v ∈ ball) : (K v iteration).val =
      fun _ : P => actualParameterBackgroundMeanIterate F hF g (q+2) (epsilon*ell)
        delta target probe iteration v s₀ := by
    rw [hKv v hv iteration hiteration,hHv]
    exact passiveParameterBackground_iterate s₀ F hF g (q+2) (epsilon*ell) delta target probe iteration v
  have rawSmooth := rawMoving (i,b)
  rw [actualProbeInitialSupply_restrict_univ Fp gp,hMovingValue] at rawSmooth
  have pairs v hv w hw := hPair v hv w hw iteration hiteration 2
  have actualPairs : ∀ v ∈ ball, ∀ w ∈ ball, ∃ Delta : ℝ,
      Delta ≤ Dpair*(‖v‖+‖w‖)*‖v-w‖ ∧ Nonempty
      (ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (2+(q+4)) (q+2) 2 Rsub Lprimary
        reserve (Bnd 2 (Rpair iteration (2+(q+4)))) (Mg 2) T
        (fun t => Fp ((B.chart b).symm t)) (fun t => hFp ((B.chart b).symm t))
        (round3ParameterNativePrimary Fp gp (B.chart b))
        (fun _ : Ep => actualParameterBackgroundMeanIterate F hF g (q+2) (epsilon*ell)
          delta target probe iteration v s₀)
        (fun _ : Ep => actualParameterBackgroundMeanIterate F hF g (q+2) (epsilon*ell)
          delta target probe iteration w s₀)
        (round3ParameterNativeDomain (B.chart b) (univ : Set (P × M)))
        (fun l => round3ParameterNativeDomain (B.chart b) (primary l))
        (A.chart i) (actualRawObserverOpen (A.chart i)
          (round3ParameterNativeDomain (B.chart b) (univ : Set (P × M))))
        ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b)) (epsilon*ell) ell Delta) := by
    intro v hv w hw
    obtain ⟨Delta,hDelta,⟨rawPair⟩⟩ := pairs v hv w hw
    refine ⟨Delta,hDelta,⟨?_⟩⟩
    have hh := rawPair (i,b)
    rw [actualProbeInitialSupply_restrict_univ Fp gp,hFixedValue v hv,hFixedValue w hw] at hh
    exact hh
  have hDpair : 0 ≤ Dpair := mul_nonneg (hDinput 2)
    (round4ParameterProbeForcedDifferenceCost_nonneg ProbeDiff
      (fun j R => Cmean j R*Dinput j) Rpair (q+4) iteration (2+(q+4)))
  have hJoint := jointMixed_passive_background_original_ball_joint s₀ F hF g
    (q+2) (epsilon*ell) delta target probe iteration (2+(q+4)) 2 Rsub Lprimary (by omega)
    reserve (Bnd 2 (Rmoving iteration (2+(q+4)))) (Mg 2) hc (hBnd _ _) (hMg _) T hT
    B amplitude ha hbuffer b p₀ hp₀ primary (A.chart i)
    ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b)) ell 0 rawSmooth (geom i)
  refine ⟨hJoint,?_⟩
  intro u hu y hy
  have hs := hSharp s₀ F hF g (epsilon*ell) delta target probe iteration B amplitude ha hbuffer
    b p₀ hp₀ primary (A.chart i) ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b))
    ell 0 Dpair hDpair (2+(q+4)) 2 Rsub Lprimary (by omega)
    reserve (Bnd 2 (Rmoving iteration (2+(q+4)))) (Mg 2) hc (hBnd _ _) (hMg _) T hT
    rawSmooth (geom i) actualPairs u hu y hy
  exact hs

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_background_sharp_of_canonical_forcing
