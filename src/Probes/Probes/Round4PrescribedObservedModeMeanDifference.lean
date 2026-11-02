import Probes.Round4PrescribedObservedCoefficientJets
import Probes.Round4PrescribedGlobalParameterSmooth
import Probes.Round4ActualProbeCoefficientColumns
import Probes.Round4ActualProbeMeanDifferenceJets
import Smoothing.ParameterRound2MeanTensorAlgebra

/-!
# Quadratic difference of one actual observed mode mean

The complete global mode is observed through its own real transition, then its
true spatial derivative coefficient is polarized. All slow joint derivatives
have the delta²*(|u|+|v|)*|u-v| bound. The cost is independent of the number of
modes: only the two chosen directions and ambient coordinate count occur.
This per-mode result is suitable for summation by the true active support count.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
variable {Eq : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
local notation "Y" => Eq × (EuclideanSpace ℝ (Fin (m+1)))
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem round4_prescribed_observed_mode_mean_difference
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 a : V)) O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (tau ell delta lam Mg Bchi Bnu : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
    (hchib : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ n, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (a : OpenPartialHomeomorph (Ep × M) X) (haO : a.target ⊆ O)
    (kappa : Y → Ep × M) (Omega Sobs : Set Y) (hOmega : IsOpen Omega) (hSobs : Sobs ⊆ Omega)
    (hsource : MapsTo kappa Omega a.source)
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) Omega)
    (hsample : ∀ y ∈ Sobs, a (kappa y) ∈ S)
    (T : ℕ → ℝ) (hTprof : ∀ k, 0 ≤ T k)
    (htransitionb : ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ Sobs,
      ell^(k-1)*‖iteratedFDeriv ℝ k (a ∘ kappa) y‖ ≤ T k)
    (phase : Ep × M → ℝ) (directions : Bool → D) (Mp : ℝ) (hMp : 0 ≤ Mp)
    (hphase : ContDiffOn ℝ ∞ (phase ∘ kappa) Omega)
    (hphib : ∀ s k, k ≤ j → ∀ y ∈ Sobs, ell^k*‖iteratedFDeriv ℝ k
      (fun z : Y => fderiv ℝ (fun x => phase (kappa (z.1,x))) z.2 (directions s)) y‖ ≤ Mp) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let amp := fun ch u y => round4PrescribedGlobalAmplitude ch label l F hF c vf tau length a u (kappa y)
    let coeff := fun u z (_ : Unit) (s : Bool) (co : Fin N) =>
      incrementsPrimaryDerivativeCoefficient (fun x => phase (kappa (z.1,x))) tau
        (fun (_ : Unit) _ => 1) (fun _ x => amp false u (z.1,x)) (fun _ x => amp true u (z.1,x))
        z.2 (directions s) co
    let CR := round4ObservationJetCost T (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) false lam Mg Bchi Bnu
    let CQ := round4ObservationJetCost T (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) true lam Mg Bchi Bnu
    let K := ∑ t : Bool × Fin N, round4CompleteCoefficientJetCost j (directions t.1) t.2 CR CQ Mp
    let mean := fun u z => incrementsOppositePrimaryContribution (coeff u z) false true
    ∀ u v, ContDiffOn ℝ ∞ (fun z => mean u z-mean v z) Omega ∧ ∀ k ≤ j, ∀ y ∈ Sobs,
      ell^k*‖iteratedFDeriv ℝ k (fun z => mean u z-mean v z) y‖ ≤
        (2^j*‖incrementsMeanBilinear (Λ:=Unit) (N:=N) false true‖*K^2)*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf amp coeff CR CQ K mean
  have hell : 0 < ell := htau.trans_le htaul
  have hTC := round4ObservationJetCost_nonneg T hTprof (j+1)
  have hCR : 0 ≤ CR := mul_nonneg hTC
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) false lam hMg hBchi hBnu)
  have hCQ : 0 ≤ CQ := mul_nonneg hTC
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) true lam hMg hBchi hBnu)
  let cost := fun t : Bool × Fin N => round4CompleteCoefficientJetCost j (directions t.1) t.2 CR CQ Mp
  have hcost (t : Bool × Fin N) : 0 ≤ cost t := by
    dsimp only [cost,round4CompleteCoefficientJetCost]
    positivity
  have hK : 0 ≤ K := Finset.sum_nonneg (fun t _ => hcost t)
  have hcostK (t : Bool × Fin N) : cost t ≤ K := Finset.single_le_sum (fun q _ => hcost q) (Finset.mem_univ t)
  have hc (s : Bool) (co : Fin N) := round4_prescribed_observed_coefficient_all_weighted_jets
    label l F hF c chi nu n length j horder O S hO hSO hA hB hG hJ hT hBR hchi hnu
    tau ell delta lam Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    hAb hBb hGb hJb hTb hBRb hchib hnub a haO kappa Omega Sobs hOmega hSobs
    hsource htransition hsample T hTprof htransitionb phase (directions s) co Mp hMp hphase (hphib s)
  have hcoeff (u : Fin p → ℝ) : ContDiffOn ℝ ∞ (coeff u) Omega := by
    apply contDiffOn_pi.2
    intro t
    apply contDiffOn_pi.2
    intro s
    exact contDiffOn_pi.2 (fun co => (hc s co u).1)
  have hcb (u : Fin p → ℝ) (k : ℕ) (hk : k ≤ j) (z : Y) (hz : z ∈ Sobs) :
      ell^k*‖iteratedFDeriv ℝ k (coeff u) z‖ ≤ (K*delta)*‖u‖ := by
    have hsm := (hcoeff u).contDiffAt (hOmega.mem_nhds (hSobs hz))
    apply parameterRound2_joint_pi_weighted_jet (coeff u) z hsm k ell _ hell (by positivity)
    intro t
    apply parameterRound2_joint_pi_weighted_jet _ z (contDiffAt_pi.1 hsm t) k ell _ hell (by positivity)
    intro s
    apply parameterRound2_joint_pi_weighted_jet _ z (contDiffAt_pi.1 (contDiffAt_pi.1 hsm t) s) k ell _ hell (by positivity)
    intro co
    exact ((hc s co u).2 k hk z hz).trans (by
      change cost (s,co)*delta*‖u‖ ≤ K*delta*‖u‖
      gcongr
      exact hcostK _)
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O :=
    (hchi.smul hnu).const_smul (-(delta*tau)/lam^2)
  have hcolumns (ch : Bool) (u : Fin p → ℝ) :
      amp ch u = finiteProbeSource (fun q => amp ch (Pi.single q 1)) u := by
    funext y
    exact congrFun (round4PrescribedGlobalAmplitude_columns ch label l F hF c vf tau length a
      (hA.mono haO) (hB.mono haO) (hBR.mono haO) (hvf.mono haO) u) (kappa y)
  have ha (ch : Bool) (u : Fin p → ℝ) := (round4_prescribed_global_amplitude_observation_jets ch label l F hF c chi nu
    n length (j+1) (by omega) O S hO hSO hA hB hG hJ hT hBR hchi hnu
    tau ell delta lam Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    hAb hBb hGb hJb hTb hBRb hchib hnub a haO kappa Omega Sobs hOmega hSobs
    hsource htransition hsample T hTprof htransitionb u).1
  have hsub (u v : Fin p → ℝ) : EqOn (fun z => coeff u z-coeff v z) (coeff (u-v)) Omega := by
    intro z hz
    have hd (ch : Bool) (q : Fin p) : DifferentiableAt ℝ (fun x => amp ch (Pi.single q 1) (z.1,x)) z.2 :=
      ((actual_joint_contDiffOn_slice _ Omega (ha ch (Pi.single q 1)) z.1).contDiffAt
        ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    have he (ch : Bool) (w : Fin p → ℝ) :
        (fun x => amp ch w (z.1,x)) =ᶠ[𝓝 z.2] finiteProbeSource (fun q x => amp ch (Pi.single q 1) (z.1,x)) w := by
      apply Filter.Eventually.of_forall
      intro x
      exact congrFun (hcolumns ch w) (z.1,x)
    funext t s co
    have hl (w : Fin p → ℝ) := round4_primary_coefficient_germ_columns
      (fun x => phase (kappa (z.1,x))) tau (fun (_ : Unit) _ => 1)
      (fun q _ x => amp false (Pi.single q 1) (z.1,x)) (fun q _ x => amp true (Pi.single q 1) (z.1,x))
      (fun _ x => amp false w (z.1,x)) (fun _ x => amp true w (z.1,x)) z.2 (directions s)
      (fun q _ => hd false q) (fun q _ => hd true q) w (fun _ => he false w) (fun _ => he true w)
    change coeff u z t s co-coeff v z t s co = coeff (u-v) z t s co
    dsimp only [coeff]
    rw [congrFun (hl u) co,congrFun (hl v) co,congrFun (hl (u-v)) co]
    simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,Finset.sum_apply,Pi.smul_apply]
  intro u v
  have hh := round4_opposite_mean_difference_slow_jets (coeff u) (coeff v) false true Omega Sobs hOmega hSobs
    (hcoeff u) (hcoeff v) j ell (K*delta) ‖u‖ ‖v‖ ‖u-v‖ hell.le (mul_nonneg hK hdelta)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hcb u) (hcb v) (by
      intro k hk z hz
      have hg := (hsub u v).eventuallyEq_of_mem (hOmega.mem_nhds (hSobs hz))
      rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
      exact hcb (u-v) k hk z hz)
  refine ⟨hh.1,?_⟩
  intro k hk z hz
  exact (hh.2 k hk z hz).trans_eq (by ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_observed_mode_mean_difference
