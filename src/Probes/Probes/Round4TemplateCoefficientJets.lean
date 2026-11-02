import Probes.Round4SupportedTemplateAmplitudes

/-!
Uniform actual coefficient and square-root jets for the fixed numerical
template cover. The coefficient operator bound is proved from the template
cover, and the same-input difference is retained exactly. The named costs
read only the observation order and one finite tensor budget, never compact
maxima of the produced amplitudes or the number of atlas charts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance coefficientRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance coefficientSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
private local instance coefficientTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance coefficientTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
variable {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}

def round4TemplateCoefficient (C : UniformActualGoodDictionaryCover K)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ E + 1)) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a).comp (C.template i).coefficients

theorem round4TemplateCoefficient_norm (C : UniformActualGoodDictionaryCover K)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ E + 1)) :
    ‖round4TemplateCoefficient C i a‖ ≤ C.coefficientBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ C.coefficientBound_pos.le
  intro g
  exact (norm_le_pi_norm ((C.template i).coefficients g) a).trans
    (((C.template i).coefficients.le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (C.bounds i).2.2.2.1 (norm_nonneg g)))

def round4TemplateRootJetConstant (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M : ℝ) : ℝ :=
  Classical.choose (increments_sqrt_reserve_scaled_jets.{0} j C.coefficientReserve
    (C.coefficientBound*M) C.coefficientReserve_pos)

def round4TemplateRootDifferenceConstant (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M : ℝ) : ℝ :=
  Classical.choose (increments_sqrt_reserve_difference_scaled_jets.{0} j C.coefficientReserve
    (C.coefficientBound*M) C.coefficientReserve_pos) * C.coefficientBound

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem round4_template_coefficient_scaled_jet
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (a : EdgePair (Module.finrank ℝ E + 1))
    (g : X → E →L[ℝ] E →L[ℝ] ℝ) (O : Set X) (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ g O) (k : ℕ) (ell M : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (x : X) (hx : x ∈ O) (hgj : ell^k*‖iteratedFDeriv ℝ k g x‖ ≤ M) :
    ell^k*‖iteratedFDeriv ℝ k (fun y => (C.template i).coefficients (g y) a) x‖ ≤
      C.coefficientBound*M :=
  (increments_fixed_linear_coefficient_scaled_jet (round4TemplateCoefficient C i a)
    O hO g hg k ell M hell hx hgj).trans
      (mul_le_mul_of_nonneg_right (round4TemplateCoefficient_norm C i a) hM)

theorem round4_template_root_scaled_jets
    (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ round4TemplateRootJetConstant C j M ∧ ∀
      (i : C.indices) (a : EdgePair (Module.finrank ℝ E + 1))
      (g : X → E →L[ℝ] E →L[ℝ] ℝ) (O S : Set X), IsOpen O → S ⊆ O →
      ContDiffOn ℝ ∞ g O → ∀ (ell : ℝ), 0 < ell →
      (∀ x ∈ S, g x ∈ (C.template i).tensorDomain) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k g x‖ ≤ M) →
      ∀ k ≤ j, ∀ x ∈ S,
        ell^k*‖iteratedFDeriv ℝ k (fun y => Real.sqrt ((C.template i).coefficients (g y) a)) x‖ ≤
          round4TemplateRootJetConstant C j M := by
  obtain ⟨hCost, hBound⟩ := Classical.choose_spec (increments_sqrt_reserve_scaled_jets.{0}
    j C.coefficientReserve (C.coefficientBound*M) C.coefficientReserve_pos)
  refine ⟨hCost, ?_⟩
  intro i a g O S hO hSO hg ell hell hdom hgj
  exact hBound O S hO hSO (fun y => (C.template i).coefficients (g y) a)
    ((round4TemplateCoefficient C i a).contDiff.comp_contDiffOn hg) ell hell
    (fun x hx => (C.bounds i).2.1.trans ((C.template i).coefficient_control (g x) (hdom x hx) a))
    (fun k hk x hx => round4_template_coefficient_scaled_jet C i a g O hO hg k ell M hell.le hM
      x (hSO hx) (hgj k hk x hx))

theorem round4_template_root_difference_scaled_jets
    (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ round4TemplateRootDifferenceConstant C j M ∧ ∀
      (i : C.indices) (a : EdgePair (Module.finrank ℝ E + 1))
      (g h : X → E →L[ℝ] E →L[ℝ] ℝ) (O S : Set X), IsOpen O → S ⊆ O →
      ContDiffOn ℝ ∞ g O → ContDiffOn ℝ ∞ h O → ∀ (ell Delta : ℝ), 0 < ell → 0 ≤ Delta →
      (∀ x ∈ S, g x ∈ (C.template i).tensorDomain ∧ h x ∈ (C.template i).tensorDomain) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k g x‖ ≤ M) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k h x‖ ≤ M) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun y => g y-h y) x‖ ≤ Delta) →
      ∀ k ≤ j, ∀ x ∈ S,
        ell^k*‖iteratedFDeriv ℝ k (fun y =>
          Real.sqrt ((C.template i).coefficients (g y) a)-
          Real.sqrt ((C.template i).coefficients (h y) a)) x‖ ≤
            round4TemplateRootDifferenceConstant C j M*Delta := by
  obtain ⟨hCost, hBound⟩ := Classical.choose_spec (increments_sqrt_reserve_difference_scaled_jets.{0}
    j C.coefficientReserve (C.coefficientBound*M) C.coefficientReserve_pos)
  refine ⟨mul_nonneg hCost C.coefficientBound_pos.le, ?_⟩
  intro i a g h O S hO hSO hg hh ell Delta hell hDelta hdom hgj hhj hdiff
  let L := round4TemplateCoefficient C i a
  have hd : (fun y => L (g y)-L (h y)) = fun y => L (g y-h y) :=
    funext fun y => (L.map_sub (g y) (h y)).symm
  have h := hBound O S hO hSO (fun y => L (g y)) (fun y => L (h y))
    (L.contDiff.comp_contDiffOn hg) (L.contDiff.comp_contDiffOn hh) ell (C.coefficientBound*Delta)
    hell (mul_nonneg C.coefficientBound_pos.le hDelta)
    (fun x hx => ⟨(C.bounds i).2.1.trans ((C.template i).coefficient_control (g x) (hdom x hx).1 a),
      (C.bounds i).2.1.trans ((C.template i).coefficient_control (h x) (hdom x hx).2 a)⟩)
    (fun k hk x hx => round4_template_coefficient_scaled_jet C i a g O hO hg k ell M hell.le hM
      x (hSO hx) (hgj k hk x hx))
    (fun k hk x hx => round4_template_coefficient_scaled_jet C i a h O hO hh k ell M hell.le hM
      x (hSO hx) (hhj k hk x hx))
    (by
      rw [hd]
      intro k hk x hx
      exact round4_template_coefficient_scaled_jet C i a (fun y => g y-h y) O hO (hg.sub hh)
        k ell Delta hell.le hDelta x (hSO hx) (hdiff k hk x hx))
  intro k hk x hx
  exact (h k hk x hx).trans_eq (by dsimp [round4TemplateRootDifferenceConstant]; ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_template_root_scaled_jets
#print axioms GlobalEmbedding.Continuation.round4_template_root_difference_scaled_jets
