import NormalPolar.JointSecondaryGroupedMean
import Probes.Round4ActualProbeMeanDifferenceJets

/-! Genuine two-parameter differences of the original-label grouped mean.
The complete reconstructed amplitudes are linear in the original external
parameter. Their actual slow joint jets and that proved linearity produce
the quadratic difference factor, including all subordinate cross terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Eq : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] {m N p r : ℕ}
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D

theorem jointGrouped_prescribed_mean_difference_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M))
    (K : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod I) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase) (i q : Fin (m+1)) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let amp := fun l ch v z => jointGroupedPrescribedAmplitude ch label F hF c vf tau length a v l (kappa z)
    let coeff := fun v z l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) v z
    let mean := fun v z => (incrementsOppositePrimaryContribution (coeff v z) i q).re
    let Kc := fun l => (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase 1
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ∀ u v : Fin p → ℝ, ContDiffOn ℝ ∞ (fun z => mean u z-mean v z) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z => mean u z-mean v z) z‖ ≤
        C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf amp coeff mean Kc C
  have hell : 0 < ell := htau.trans_le htaul
  have hub (u : Fin p → ℝ) (k : ℕ) (_hk : k ≤ j) (z : Y) (_hz : z ∈ S) :
      ell^k*‖iteratedFDeriv ℝ k (fun _ : Y => u) z‖ ≤ ‖u‖ := by
    cases k with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,one_mul]; exact le_rfl
    | succ k => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,mul_zero] using norm_nonneg u
  have hraw (u : Fin p → ℝ) := jointGrouped_prescribed_coefficient_from_raw label F hF c chi nu a W K hW
    n length j horder tau ell delta weight Mg Bchi Bnu Mphase ‖u‖ htau htaul hell1
    hMg hdelta hBchi hBnu hMphase (norm_nonneg u) kappa Omega S hOmega hS hkappa hmap
    T hT phase profiles (fun _ => u) contDiffOn_const (hub u)
  have hcoeff (u : Fin p → ℝ) : ContDiffOn ℝ ∞ (coeff u) Omega :=
    contDiffOn_pi.2 (fun l => (hraw u l).1)
  have hKc (l : Fin r) : 0 ≤ Kc l := mul_nonneg (Nat.cast_nonneg _)
    (jointSecondary_variable_prescribed_coefficient_cost_nonneg m N p n length j T
      (weight l) Mg Bchi Bnu Mphase 1 hT hMg hBchi hBnu hMphase zero_le_one)
  let Ksum := ∑ l, Kc l
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg (fun l _ => hKc l)
  have hKle (l : Fin r) : Kc l ≤ Ksum := Finset.single_le_sum (fun l _ => hKc l) (Finset.mem_univ l)
  have hbound (u : Fin p → ℝ) (k : ℕ) (hk : k ≤ j) (z : Y) (hz : z ∈ S) :
      ell^k*‖iteratedFDeriv ℝ k (coeff u) z‖ ≤ (Ksum*delta)*‖u‖ := by
    apply parameterRound2_joint_pi_weighted_jet (coeff u) z
      ((hcoeff u).contDiffAt (hOmega.mem_nhds (hS hz))) k ell _ hell (by positivity)
    intro l
    have hb := (hraw u l).2 k hk z hz
    have he : ((Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j
        T (weight l) Mg Bchi Bnu Mphase ‖u‖)*delta = (Kc l*delta)*‖u‖ := by
      dsimp only [Kc,actualVariablePrescribedCoefficientCost]
      ring
    exact hb.trans (he.le.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hKle l) hdelta) (norm_nonneg u)))
  have hamp (l : Fin r) (ch : Bool) (u : Fin p → ℝ) : ContDiffOn ℝ ∞ (amp l ch u) Omega := by
    change ContDiffOn ℝ ∞ (fun z => ∑ s, round4PrescribedGlobalAmplitude ch label l F hF
      (c l s) (vf l s) tau length (a l s) u (kappa z)) Omega
    exact ContDiffOn.sum (fun s _ =>
      ((actualRepairModelFirstDefect_prescribed_amplitude_regular ch label l F hF
        (c l s) (chi l s) (nu l s) (a l s) W (K l s) hW n (j+1) length
        ell Mg Bchi Bnu tau delta (weight l) (profiles.raw l s) u).1.comp hkappa hmap).contDiffOn)
  have hcolumns (l : Fin r) (ch : Bool) (u : Fin p → ℝ) :
      amp l ch u = fun y => ∑ k, u k • amp l ch (Pi.single k 1) y := by
    funext y
    exact congrFun (jointGroupedPrescribedAmplitude_columns ch label F hF c vf tau length a
      (fun l s => (profiles.raw l s).A_smooth) (fun l s => (profiles.raw l s).B_smooth)
      (fun l s => (profiles.raw l s).BR_smooth)
      (fun l s => ((profiles.raw l s).cutoff_smooth.smul (profiles.raw l s).normal_smooth).const_smul
        (-(delta*tau)/(weight l)^2)) u l) (kappa y)
  have hsub (u v : Fin p → ℝ) : EqOn (fun z => coeff u z-coeff v z) (coeff (u-v)) Omega := by
    intro z hz
    funext l
    have hc (w : Fin p → ℝ) := actual_diagonal_physical_coefficient_columns
      (phase l ∘ kappa) tau (amp l) Omega hOmega (fun ch k => hamp l ch (Pi.single k 1))
      (hcolumns l) w z hz
    change actualDiagonalPhysicalCoefficient _ _ _ u z-actualDiagonalPhysicalCoefficient _ _ _ v z =
      actualDiagonalPhysicalCoefficient _ _ _ (u-v) z
    rw [hc u,hc v,hc (u-v)]
    simp only [Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
  intro u v
  have hh := round4_opposite_mean_difference_slow_jets (coeff u) (coeff v) i q Omega S hOmega hS
    (hcoeff u) (hcoeff v) j ell (Ksum*delta) ‖u‖ ‖v‖ ‖u-v‖ hell.le
    (mul_nonneg hKsum hdelta) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (hbound u) (hbound v) (by
      intro k hk z hz
      rw [(((hsub u v).eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
      exact hbound (u-v) k hk z hz)
  let rawDiff := fun z => incrementsOppositePrimaryContribution (coeff u z) i q-
    incrementsOppositePrimaryContribution (coeff v z) i q
  have heq : (fun z => mean u z-mean v z) = Complex.reCLM ∘ rawDiff := by
    funext z
    exact (map_sub Complex.reCLM _ _).symm
  rw [heq]
  refine ⟨Complex.reCLM.contDiff.comp_contDiffOn hh.1,?_⟩
  intro k hk z hz
  have hb := slow_linear_jet_bound Complex.reCLM Omega hOmega rawDiff hh.1 k ell _ hell.le
    z (hS hz) (hh.2 k hk z hz)
  simp only [Complex.reCLM_norm,one_mul] at hb
  exact hb.trans_eq (by dsimp only [C,Ksum]; ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_mean_difference_from_raw
