import Probes.Round4UniformTemplateNativeProfiles

/-! The same host phase chart has an order-zero profile from the original
bounded host center. This derives the full source-domain value bound from
its actual outer ball; it does not assume a separate coordinate-value budget. -/
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

theorem round4_uniform_template_chart_bounded_host_profiles
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
    (O : Set X) (x : X) (ell : ℝ)
    (i : (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (b : Round4UniformTemplateChart hdim R mu c H hmu hc f O x ell i a)
    (B0 : ℝ) (hx : ‖x‖ ≤ B0) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc
    (∀ z ∈ b.chart.source, ‖z‖ ≤ B0+ell) ∧
    (∀ j z, z ∈ b.chart.source → ‖iteratedFDeriv ℝ j b.chart z‖ ≤
      round4LinearPhaseForwardProfile C.covectorBound (B0+ell) j) ∧
    (∀ j z, z ∈ b.chart.target → ‖iteratedFDeriv ℝ j b.chart.symm z‖ ≤
      round4LinearPhaseInverseProfile eta C.covectorBound (B0+ell) j) := by
  intro C eta
  have hbound (z) (hz : z ∈ b.chart.source) : ‖z‖ ≤ B0+ell := by
    have hd : ‖z-x‖ < ell := by simpa only [Metric.mem_ball,dist_eq_norm] using b.outer hz
    calc
      ‖z‖ ≤ ‖z-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (z-x) x
      _ ≤ ell+B0 := add_le_add hd.le hx
      _ = B0+ell := add_comm _ _
  exact ⟨hbound,round4_uniform_template_chart_native_profiles hdim R mu c H hmu hc
    f O x ell i a b (B0+ell) hbound⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_chart_bounded_host_profiles
