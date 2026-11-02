import NormalPolar.ParameterDisplacementVariableCoefficient
import Mathlib.Analysis.Complex.OperatorNorm

/-! The actual conjugate-pair mean receives every joint derivative of its
variable coefficient field. Both ordered terms and the original quarter
factor are retained through the proved diagonal bilinear identity. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {Y Λ J : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [Fintype Λ] [Fintype J] {N : ℕ}

theorem actual_variable_coefficient_mean_slow_jets
    (coeff : Y → Λ → J → Fin N → ℂ) (Omega S : Set Y)
    (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (j : ℕ) (ell delta : ℝ) (K : Λ → ℝ) (hell : 0 < ell) (hdelta : 0 ≤ delta)
    (hK : ∀ l, 0 ≤ K l)
    (hc : ∀ l, ContDiffOn ℝ ∞ (fun z => coeff z l) Omega)
    (hcb : ∀ l k, k ≤ j → ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (fun z => coeff z l) z‖ ≤ K l*delta)
    (i q : J) :
    let mean := fun z => (incrementsOppositePrimaryContribution (coeff z) i q).re
    let C := 2^j*‖incrementsMeanBilinear (Λ := Λ) (N := N) i q‖*(∑ l, K l)^2
    ContDiffOn ℝ ∞ mean Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k mean z‖ ≤ C*delta^2 := by
  intro mean C
  let Ksum := ∑ l, K l
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg (fun l _ => hK l)
  have hKle (l : Λ) : K l ≤ Ksum := Finset.single_le_sum (fun q _ => hK q) (Finset.mem_univ l)
  have hcoeff : ContDiffOn ℝ ∞ coeff Omega := contDiffOn_pi.2 hc
  have hbound (k : ℕ) (hk : k ≤ j) (z : Y) (hz : z ∈ S) :
      ell^k*‖iteratedFDeriv ℝ k coeff z‖ ≤ Ksum*delta := by
    apply parameterRound2_joint_pi_weighted_jet coeff z
      (hcoeff.contDiffAt (hOmega.mem_nhds (hS hz))) k ell _ hell (mul_nonneg hKsum hdelta)
    intro l
    exact (hcb l k hk z hz).trans (mul_le_mul_of_nonneg_right (hKle l) hdelta)
  let L := incrementsMeanBilinear (Λ := Λ) (N := N) i q
  let rawMean := fun z => L (coeff z) (coeff z)
  have hraw : ContDiffOn ℝ ∞ rawMean Omega := (L.contDiff.comp_contDiffOn hcoeff).clm_apply hcoeff
  have he : mean = Complex.reCLM ∘ rawMean := by
    funext z
    exact congrArg Complex.re (incrementsMeanBilinear_diagonal (coeff z) i q).symm
  rw [he]
  refine ⟨Complex.reCLM.contDiff.comp_contDiffOn hraw,?_⟩
  intro k hk z hz
  have hb := slow_bilinear_jet_bound_norm L Omega hOmega coeff coeff hcoeff hcoeff k ell
    (Ksum*delta) (Ksum*delta) hell.le z (hS hz)
    (fun a ha => hbound a (ha.trans hk) z hz) (fun a ha => hbound a (ha.trans hk) z hz)
  have hr := slow_linear_jet_bound Complex.reCLM Omega hOmega rawMean hraw k ell _ hell.le z (hS hz) hb
  simp only [Complex.reCLM_norm,one_mul] at hr
  calc
    _ ≤ 2^k*(‖L‖*(Ksum*delta))*(Ksum*delta) := hr
    _ = (2^k*‖L‖*Ksum^2)*delta^2 := by ring
    _ ≤ C*delta^2 := by dsimp only [C,L,Ksum]; gcongr; norm_num

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_variable_coefficient_mean_slow_jets
