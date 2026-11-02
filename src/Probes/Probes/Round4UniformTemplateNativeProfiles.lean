import Probes.Round4UniformTemplateBlock

/-!
Order-zero and higher native profiles of the very same template chart used
by the actual finite refinement. The coordinate-value bound is primitive;
there is no inference from bounded phase derivatives to bounded phase value,
and no replacement by an independently chosen chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativeProfilesRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance nativeProfilesSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance nativeProfilesTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance nativeProfilesTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem round4_uniform_template_chart_native_profiles
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
    (O : Set X) (x : X) (ell : ℝ)
    (i : (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (b : Round4UniformTemplateChart hdim R mu c H hmu hc f O x ell i a)
    (B : ℝ) (hB : ∀ z ∈ b.chart.source, ‖z‖ ≤ B) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc
    (∀ j z, z ∈ b.chart.source → ‖iteratedFDeriv ℝ j b.chart z‖ ≤
      round4LinearPhaseForwardProfile C.covectorBound B j) ∧
    (∀ j z, z ∈ b.chart.target → ‖iteratedFDeriv ℝ j b.chart.symm z‖ ≤
      round4LinearPhaseInverseProfile eta C.covectorBound B j) := by
  intro C eta
  constructor
  · intro j z hz
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 0 b.chart z‖ ≤ 2*(1+2*C.covectorBound)*B
      rw [norm_iteratedFDeriv_zero]
      exact (b.forward_value z hz).trans
        (mul_le_mul_of_nonneg_left (hB z hz) (by have := C.covectorBound_pos; positivity))
    | succ j =>
      cases j with
      | zero =>
        change ‖iteratedFDeriv ℝ 1 b.chart z‖ ≤ 2*(1+2*C.covectorBound)
        rw [norm_iteratedFDeriv_one]
        exact b.forward_bound z hz
      | succ j =>
        change ‖iteratedFDeriv ℝ (j+1+1) b.chart z‖ ≤ 0
        rw [b.forward_higher_zero (j+1) (by omega) z hz, norm_zero]
  · intro j z hz
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 0 b.chart.symm z‖ ≤ B
      rw [norm_iteratedFDeriv_zero]
      exact hB _ (b.chart.map_target hz)
    | succ j =>
      cases j with
      | zero =>
        change ‖iteratedFDeriv ℝ 1 b.chart.symm z‖ ≤
          2*actualPhaseInverseConstant eta (2*C.covectorBound)
        rw [norm_iteratedFDeriv_one]
        exact b.inverse_bound z hz
      | succ j =>
        change ‖iteratedFDeriv ℝ (j+1+1) b.chart.symm z‖ ≤ 0
        rw [b.inverse_higher_zero (j+1) (by omega) z hz, norm_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_chart_native_profiles
