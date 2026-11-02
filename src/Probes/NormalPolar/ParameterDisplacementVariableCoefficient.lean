import NormalPolar.ParameterDisplacementVariableColumns
import Probes.Round4ActualProbeCoefficientColumns
import Probes.ActualIncrementJointDirectionalJets
import Smoothing.ParameterRound2MeanTensorAlgebra

/-! Genuine diagonal substitution into the full physical derivative
coefficient. The coefficient differentiates the original fixed-parameter
spatial amplitude first; the resulting field then receives the variable
parameter and all of its joint derivatives. No phase regularity is used in
the finite-column identity. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {Eq : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] {m N p : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Y" => Eq × D

def actualDiagonalPhysicalCoefficient (phase : Y → ℝ) (tau : ℝ)
    (amp : Bool → (Fin p → ℝ) → Y → V) (u : Fin p → ℝ) (z : Y)
    (i : Fin (m+1)) : Fin N → ℂ :=
  incrementsPrimaryDerivativeCoefficient (fun x => phase (z.1,x)) tau (fun (_ : Unit) _ => 1)
    (fun (_ : Unit) x => amp false u (z.1,x)) (fun (_ : Unit) x => amp true u (z.1,x))
    z.2 (EuclideanSpace.single i 1)

theorem actual_diagonal_physical_coefficient_columns
    (phase : Y → ℝ) (tau : ℝ) (amp : Bool → (Fin p → ℝ) → Y → V)
    (Omega : Set Y) (hOmega : IsOpen Omega)
    (hamp : ∀ ch q, ContDiffOn ℝ ∞ (amp ch (Pi.single q 1)) Omega)
    (hcolumns : ∀ ch v, amp ch v = fun y => ∑ q, v q • amp ch (Pi.single q 1) y)
    (u : Fin p → ℝ) (z : Y) (hz : z ∈ Omega) :
    actualDiagonalPhysicalCoefficient phase tau amp u z =
      ∑ q, u q • actualDiagonalPhysicalCoefficient phase tau amp (Pi.single q 1) z := by
  have hd (ch : Bool) (q : Fin p) :
      DifferentiableAt ℝ (fun x => amp ch (Pi.single q 1) (z.1,x)) z.2 :=
    ((actual_joint_contDiffOn_slice _ Omega (hamp ch q) z.1).contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
  have he (ch : Bool) : (fun x => amp ch u (z.1,x)) =ᶠ[𝓝 z.2]
      finiteProbeSource (fun q x => amp ch (Pi.single q 1) (z.1,x)) u := by
    apply Filter.Eventually.of_forall
    intro x
    exact congrFun (hcolumns ch u) (z.1,x)
  funext i
  simpa only [actualDiagonalPhysicalCoefficient, Finset.sum_apply, Pi.smul_apply] using
    round4_primary_coefficient_germ_columns (fun x => phase (z.1,x)) tau
    (fun (_ : Unit) _ => 1)
    (fun q (_ : Unit) x => amp false (Pi.single q 1) (z.1,x))
    (fun q (_ : Unit) x => amp true (Pi.single q 1) (z.1,x))
    (fun (_ : Unit) x => amp false u (z.1,x)) (fun (_ : Unit) x => amp true u (z.1,x))
    z.2 (EuclideanSpace.single i 1) (fun q _ => hd false q) (fun q _ => hd true q) u
    (fun _ => he false) (fun _ => he true)

theorem actual_variable_diagonal_coefficient_slow_jets
    (phase : Y → ℝ) (tau : ℝ) (amp : Bool → (Fin p → ℝ) → Y → V)
    (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hamp : ∀ ch q, ContDiffOn ℝ ∞ (amp ch (Pi.single q 1)) Omega)
    (hcolumns : ∀ ch v, amp ch v = fun y => ∑ q, v q • amp ch (Pi.single q 1) y)
    (j : ℕ) (ell Ku Kc delta : ℝ) (hell : 0 < ell) (hKu : 0 ≤ Ku) (hKc : 0 ≤ Kc) (hdelta : 0 ≤ delta)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k u z‖ ≤ Ku)
    (hc : ∀ q, ContDiffOn ℝ ∞ (actualDiagonalPhysicalCoefficient phase tau amp (Pi.single q 1)) Omega)
    (hcb : ∀ q k, k ≤ j → ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (actualDiagonalPhysicalCoefficient phase tau amp (Pi.single q 1)) z‖ ≤ Kc*delta) :
    let f := fun z => actualDiagonalPhysicalCoefficient phase tau amp (u z) z
    ContDiffOn ℝ ∞ f Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ (((p:ℝ)*2^j*Ku)*Kc)*delta := by
  intro f
  let cols := fun q => actualDiagonalPhysicalCoefficient phase tau amp (Pi.single q 1)
  have he : EqOn f (fun z => ∑ q, u z q • cols q z) Omega :=
    fun z hz => actual_diagonal_physical_coefficient_columns phase tau amp Omega hOmega hamp hcolumns (u z) z hz
  have hh := actual_variable_columns_weighted_jets j u cols Omega S hOmega hS hu hc
    ell ell Ku (Kc*delta) hell le_rfl hKu (mul_nonneg hKc hdelta) hub hcb
  refine ⟨hh.1.congr he,?_⟩
  intro k hk z hz
  rw [((he.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  exact (hh.2 k hk z hz).trans_eq (by ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_diagonal_physical_coefficient_columns
#print axioms GlobalEmbedding.Continuation.actual_variable_diagonal_coefficient_slow_jets
