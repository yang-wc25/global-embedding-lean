import NormalPolar.ParameterDisplacementVariableCoefficient
import NormalPolar.ActualRepairModelFirstDefectPrescribedCoefficients

/-! Slow joint derivatives of the complete prescribed physical coefficient
after a genuine variable parameter substitution. The fixed-column bounds are
produced from the same original raw reconstructed source, including both
channels and inactive zero germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
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

def actualVariablePrescribedCoefficientCost (m N p n length j : ℕ)
    (T : ℕ → ℝ) (weight Mg Bchi Bnu Mphase Ku : ℝ) : ℝ :=
  ((p:ℝ)*2^j*Ku)*actualRepairModelFirstDefectPrescribedCoefficientCost
    m N n length j T weight Mg Bchi Bnu Mphase 1

theorem actual_prescribed_variable_coefficient_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod I) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k u z‖ ≤ Ku) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let amp := fun l ch v z => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) v (kappa z)
    ∀ l, let f := fun z => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) (u z) z
      ContDiffOn ℝ ∞ f Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
        ell^k*‖iteratedFDeriv ℝ k f z‖ ≤
          actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku*delta := by
  intro vf amp l
  have hsingle (q : Fin p) : ‖(Pi.single q (1:ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hraw (q : Fin p) := actualRepairModelFirstDefect_prescribed_coefficients_from_raw label
    F hF c chi nu a W K hW n length j horder tau ell delta weight Mg Bchi Bnu 1 Mphase
    htau htaul hell1 hMg hdelta hBchi hBnu zero_le_one hMphase
    kappa Omega S hOmega hS hkappa hmap T hT phase profiles (Pi.single q 1) (hsingle q) l
  have hamp (ch : Bool) (q : Fin p) : ContDiffOn ℝ ∞ (amp l ch (Pi.single q 1)) Omega :=
    ((actualRepairModelFirstDefect_prescribed_amplitude_regular ch label l F hF
      (c l) (chi l) (nu l) (a l) W (K l) hW n (j+1) length ell Mg Bchi Bnu tau delta
      (weight l) (profiles.raw l) (Pi.single q 1)).1.comp hkappa hmap).contDiffOn
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target :=
    (((profiles.raw l).cutoff_smooth.smul (profiles.raw l).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have hcolumns (ch : Bool) (v : Fin p → ℝ) :
      amp l ch v = fun y => ∑ q, v q • amp l ch (Pi.single q 1) y := by
    funext y
    exact congrFun (round4PrescribedGlobalAmplitude_columns ch label l F hF (c l) (vf l)
      tau length (a l) (profiles.raw l).A_smooth (profiles.raw l).B_smooth
      (profiles.raw l).BR_smooth hvf v) (kappa y)
  let Kc := actualRepairModelFirstDefectPrescribedCoefficientCost m N n length j T (weight l) Mg Bchi Bnu Mphase 1
  have hKc : 0 ≤ Kc := actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg
    m N n length j T (weight l) Mg Bchi Bnu Mphase 1 hT hMg hBchi hBnu hMphase zero_le_one
  exact actual_variable_diagonal_coefficient_slow_jets (phase l ∘ kappa) tau (amp l)
    Omega S hOmega hS hamp hcolumns j ell Ku Kc delta (htau.trans_le htaul) hKu hKc hdelta u hu hub
    (fun q => (hraw q).1) (fun q => (hraw q).2.1)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_prescribed_variable_coefficient_from_raw
