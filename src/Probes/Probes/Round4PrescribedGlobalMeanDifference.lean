import Probes.Round4PrescribedObservedModeMeanDifference
import Probes.Round4PrescribedObservedZeroGerm
import Smoothing.ParameterTransferBounds

/-!
# Actual complete global mean differences with true local multiplicity

Each mode uses its own source chart and actual observer transition. Primitive
source profiles produce the active estimates; primitive relative source support
produces every inactive coefficient germ. The finite sum is bounded by the true
active support count, never by the total number of charts or parameter columns.
The numerical cost premise compares explicit primitive-profile expressions; no
mean, coefficient, or reconstruction estimate is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Filter Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Eq : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D
local notation "Pspace" => Fin p → ℝ

theorem round4_prescribed_global_mean_difference_active_jets
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (chi l) → (a l).symm z ∈ K l)
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (Slocal : Fin r → Set X) (hSloc : ∀ l, Slocal l ⊆ (a l).target)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I:=I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun d : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 d : V)) (a l).target)
    (hchi : ∀ l, ContDiffOn ℝ ∞ (chi l) (a l).target)
    (hnu : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (nu l z.1 z.2 : V)) (a l).target)
    (tau ell delta Mg Mp : ℝ) (weight Bchi Bnu : Fin r → ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hMp : 0 ≤ Mp)
    (hBchi : ∀ l, 0 ≤ Bchi l) (hBnu : ∀ l, 0 ≤ Bnu l)
    (hAb : ∀ l k, k ≤ n → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ l k, k ≤ n → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c l w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I:=I) (F w.1) (c l w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c l w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fun d : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c l w.1) w.2 0 d : V)) z‖ ≤ Mg)
    (hchib : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k (chi l) z‖ ≤ Bchi l)
    (hnub : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (nu l w.1 w.2 : V)) z‖ ≤ Bnu l)
    (kappa : Y → Ep × M) (Omega Sobs : Set Y) (hOmega : IsOpen Omega) (hSobs : Sobs ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (Obs : Fin r → Set Y) (hObs : ∀ l, IsOpen (Obs l))
    (hactive : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ Obs l)
    (hsource : ∀ l, MapsTo kappa (Obs l) (a l).source)
    (htransition : ∀ l, ContDiffOn ℝ ∞ (a l ∘ kappa) (Obs l))
    (hsample : ∀ l y, y ∈ Sobs → kappa y ∈ K l → a l (kappa y) ∈ Slocal l)
    (T : Fin r → ℕ → ℝ) (hTprof : ∀ l k, 0 ≤ T l k)
    (htransitionb : ∀ l k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ Sobs, kappa y ∈ K l →
      ell^(k-1)*‖iteratedFDeriv ℝ k (a l ∘ kappa) y‖ ≤ T l k)
    (directions : Bool → D)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (Obs l))
    (hphib : ∀ l s k, k ≤ j → ∀ y ∈ Sobs, kappa y ∈ K l → ell^k*‖iteratedFDeriv ℝ k
      (fun z : Y => fderiv ℝ (fun x => phase l (kappa (z.1,x))) z.2 (directions s)) y‖ ≤ Mp)
    (multiplicity : ℕ)
    (hmultiplicity : ∀ y ∈ Sobs, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ multiplicity)
    (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ l,
      let CR := round4ObservationJetCost (T l) (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) false (weight l) Mg (Bchi l) (Bnu l)
      let CQ := round4ObservationJetCost (T l) (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) true (weight l) Mg (Bchi l) (Bnu l)
      let Kc := ∑ t : Bool × Fin N, round4CompleteCoefficientJetCost j (directions t.1) t.2 CR CQ Mp
      2^j*‖incrementsMeanBilinear (Λ:=Unit) (N:=N) false true‖*Kc^2 ≤ C) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let amp := fun ch u l y => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) u (kappa y)
    let coeff := fun u z l (s : Bool) (co : Fin N) => incrementsPrimaryDerivativeCoefficient
      (fun x => phase l (kappa (z.1,x))) tau (fun (_ : Unit) _ => 1)
      (fun _ x => amp false u l (z.1,x)) (fun _ x => amp true u l (z.1,x)) z.2 (directions s) co
    let mean := fun u z => incrementsOppositePrimaryContribution (coeff u z) false true
    ∀ u v, ContDiffOn ℝ ∞ (fun z => mean u z-mean v z) Omega ∧ ∀ k ≤ j, ∀ y ∈ Sobs,
      ell^k*‖iteratedFDeriv ℝ k (fun z => mean u z-mean v z) y‖ ≤
        (multiplicity:ℝ)*C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  classical
  intro vf amp coeff mean u v
  have hell : 0 < ell := htau.trans_le htaul
  let mode := fun w l z => incrementsOppositePrimaryContribution (fun (_ : Unit) s => coeff w z l s) false true
  let diff := fun l z => mode u l z-mode v l z
  let Budget := C*delta^2*(‖u‖+‖v‖)*‖u-v‖
  have hBudget : 0 ≤ Budget := by dsimp only [Budget]; positivity
  have ha (l : Fin r) := round4_prescribed_observed_mode_mean_difference label l F hF (c l) (chi l) (nu l)
    n length j horder (a l).target (Slocal l) (a l).open_target (hSloc l)
    (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hchi l) (hnu l)
    tau ell delta (weight l) Mg (Bchi l) (Bnu l) htau htaul hell1 hMg hdelta (hBchi l) (hBnu l)
    (hAb l) (hBb l) (hGb l) (hJb l) (hTb l) (hBRb l) (hchib l) (hnub l)
    (a l) Subset.rfl kappa (Obs l) (Sobs ∩ kappa ⁻¹' K l) (hObs l)
    (fun y hy => hactive l ⟨hSobs hy.1,hy.2⟩) (hsource l) (htransition l)
    (fun y hy => hsample l y hy.1 hy.2) (T l) (hTprof l)
    (fun k hk hkj y hy => htransitionb l k hk hkj y hy.1 hy.2)
    (phase l) directions Mp hMp (hphase l)
    (fun s k hk y hy => hphib l s k hk y hy.1 hy.2) u v
  have hzero (l : Fin r) (z : Y) (hz : z ∈ Omega) (hn : kappa z ∉ K l) : diff l =ᶠ[𝓝 z] 0 := by
    have hvf : ContDiffOn ℝ ∞ (fun w : X => (vf l w.1 w.2 : V)) (a l).target :=
      ((hchi l).smul (hnu l)).const_smul (-(delta*tau)/(weight l)^2)
    have hs : ∀ w ∈ (a l).target, w ∈ tsupport (fun y : X => (vf l y.1 y.2 : V)) → (a l).symm w ∈ K l := by
      intro w hw hn
      apply hinput l w hw
      exact ((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hn
    have hzmode (w : Pspace) : mode w l =ᶠ[𝓝 z] 0 :=
      round4_prescribed_global_mode_mean_inactive_germ label l F hF (c l) (vf l) tau length (a l) W (K l)
        hW (hK l) (hKsource l) (hchart l) (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) hvf hs
        w kappa z (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmap hz) hn (phase l) directions false true
    filter_upwards [hzmode u,hzmode v] with y hu hv
    simp only [diff,hu,hv,Pi.zero_apply,sub_zero]
  have hreg (l : Fin r) : ContDiffOn ℝ ∞ (diff l) Omega := by
    intro z hz
    by_cases hn : kappa z ∈ K l
    · exact ((ha l).1.contDiffAt ((hObs l).mem_nhds (hactive l ⟨hz,hn⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero l z hz hn)).contDiffWithinAt
  have hsum : (fun z => mean u z-mean v z) = fun z => ∑ l, diff l z := by
    funext z
    simp only [mean,diff,mode,incrementsOppositePrimaryContribution,Finset.univ_unique,Finset.sum_singleton,
      Finset.sum_sub_distrib]
  rw [hsum]
  refine ⟨ContDiffOn.sum (fun l _ => hreg l),?_⟩
  intro k hk z hz
  let active := Finset.univ.filter (fun l => kappa z ∈ K l)
  have hb (l : Fin r) (hl : l ∈ active) : ell^k*‖iteratedFDeriv ℝ k (diff l) z‖ ≤ Budget := by
    have hh := (ha l).2 k hk z ⟨hz,(Finset.mem_filter.mp hl).2⟩
    exact hh.trans (by
      dsimp only [Budget]
      gcongr
      exact hcost l)
  have hn : ∀ l ∉ active, diff l =ᶠ[𝓝 z] (fun _ => 0) := by
    intro l hl
    apply hzero l z (hSobs hz)
    intro h
    exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hh := parameter_finite_sum_jet_le diff z active multiplicity k (Budget/ell^k)
    (hmultiplicity z hz) (div_nonneg hBudget (pow_nonneg hell.le _))
    (fun l _ => (hreg l).contDiffAt (hOmega.mem_nhds (hSobs hz))) hn
    (fun l hl => (le_div_iff₀ (pow_pos hell _)).2 (by simpa only [mul_comm] using hb l hl))
  calc
    _ ≤ ell^k*((multiplicity:ℝ)*(Budget/ell^k)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hell.le _)
    _ = (multiplicity:ℝ)*C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
      dsimp only [Budget]
      field_simp [ne_of_gt hell]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_mean_difference_active_jets
