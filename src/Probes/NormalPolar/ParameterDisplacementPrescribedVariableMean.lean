import NormalPolar.ParameterDisplacementPrescribedVariableCoefficient
import NormalPolar.ParameterDisplacementVariableMean

/-! The actual variable-parameter prescribed opposite mean receives its full
slow joint budget from the same primitive reconstructed source. The two
ordered conjugate terms and quarter factor are preserved. -/

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

theorem actual_prescribed_variable_mean_from_raw
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
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k u z‖ ≤ Ku) (i q : Fin (m+1)) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let amp := fun l ch v z => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) v (kappa z)
    let coeff := fun z l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) (u z) z
    let mean := fun z => (incrementsOppositePrimaryContribution (coeff z) i q).re
    let Kc := fun l => actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ContDiffOn ℝ ∞ mean Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k mean z‖ ≤ C*delta^2 := by
  intro vf amp coeff mean Kc C
  have hraw := actual_prescribed_variable_coefficient_from_raw label F hF c chi nu a W K hW
    n length j horder tau ell delta weight Mg Bchi Bnu Mphase Ku htau htaul hell1
    hMg hdelta hBchi hBnu hMphase hKu kappa Omega S hOmega hS hkappa hmap T hT phase profiles u hu hub
  have hKc (l : Fin r) : 0 ≤ Kc l := by
    exact mul_nonneg (by positivity) (actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg
      m N n length j T (weight l) Mg Bchi Bnu Mphase 1 hT hMg hBchi hBnu hMphase zero_le_one)
  exact actual_variable_coefficient_mean_slow_jets coeff Omega S hOmega hS j ell delta Kc
    (htau.trans_le htaul) hdelta hKc (fun l => (hraw l).1) (fun l => (hraw l).2) i q

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_prescribed_variable_mean_from_raw
