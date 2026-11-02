import Probes.Round4UniformTemplateRadius
import Probes.ActualIncrementSampleNormalTransfer
import Probes.ActualSpatialJointJets
import GlobalEmbedding.Offline.ActualHessianJet

/-!
The uniform dictionary radius applied to the actual normal second form.
Only the actual first spatial derivative, actual spatial Hessian, their first
joint derivatives, a first-frame reserve, and the target tensor's first
derivative are consumed. Thus the map input stops at order three. The
projected normal Hessian, the quotient operator and its Lipschitz constant
are derived, with the original symmetric-square normalization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function Manifold
open scoped TensorProduct Topology ContDiff NNReal
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance fieldRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance fieldSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance fieldFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance fieldFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance fieldHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  inferInstance
private local instance fieldHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  inferInstance
private local instance fieldTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  inferInstance
private local instance fieldTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  inferInstance

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def round4ActualPhaseOperatorInChart (F : Ep → M → V)
    (e : Ep → OpenPartialHomeomorph M D) (z : X) : SymmetricSquare D →L[ℝ] V :=
  actualHessianLift (actualNormalHessianInChart F e z)

theorem round4_actual_phase_operator_product
    (F : Ep → M → V) (e : Ep → OpenPartialHomeomorph M D)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (v w : D) :
    round4ActualPhaseOperatorInChart F e z (symmetricSquareProduct D v w) =
      actualNormalHessianInChart F e z v w := by
  have hs : ContDiffAt ℝ ∞ (F z.1 ∘ (e z.1).symm) z.2 := by
    have h := (hJoint.contDiffAt (hO.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)
    exact h
  apply actualHessianLift_product_of_symmetric
  intro a b
  exact congrArg (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
    (hs.isSymmSndFDerivAt (by simp) a b)

/-- On the original coordinate generators, this operator is exactly the
original true second form, embedded into the ambient Euclidean space. -/
theorem round4_actual_phase_operator_original_rows
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ (e z.1).target) (i j : Fin (m+1)) :
    round4ActualPhaseOperatorInChart F e z
        (symmetricSquareProduct D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 i j : V) := by
  rw [round4_actual_phase_operator_product F e O hO hJoint z hz]
  exact (actual_increment_secondForm_chart (F z.1) (hF z.1)
    (e z.1) (he z.1) z.2 hcoord i j).symm

def round4ActualTemplateFieldLipschitz (m N : ℕ) (c MA MH : ℝ)
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) (MT : ℝ≥0) : ℝ≥0 :=
  max (‖actualHessianLift (E := EuclideanSpace ℝ (Fin (m+1)))
      (F := EuclideanSpace ℝ (Fin N))‖₊ *
    ⟨actualIncrementSecondFormConstant m N 1 c MA MH,
      actualIncrementSecondFormConstant_nonneg m N 1 hc hMA hMH⟩) MT

theorem round4_actual_template_field_lipschitz
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (c MA MH : ℝ) (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (MT : ℝ≥0)
    (hA : ∀ z ∈ O, DifferentiableAt ℝ A z)
    (hAT : ∀ z ∈ O, ‖fderiv ℝ A z‖₊ ≤ MT) :
    LipschitzOnWith (round4ActualTemplateFieldLipschitz m N c MA MH hc hMA hMH MT)
      (fun z => (round4ActualPhaseOperatorInChart F e z, A z)) O := by
  have hs := incrementsJointSpatialJets_bridge
    (fun z : X => F z.1 ((e z.1).symm z.2)) O hO hJoint
  obtain ⟨hQ, hQj⟩ := actual_increment_projected_hessian_slow_jets F hF e he O hO
    hcoord hs.2.1 hs.2.2 1 1 c MA MH (by norm_num) hc hMA hMH hreserve
    (by simpa only [one_pow, one_mul] using hAj)
    (by simpa only [one_pow, one_mul] using hHj)
  change ContDiffOn ℝ ∞ (actualNormalHessianInChart F e) O at hQ
  let K : ℝ≥0 := ⟨actualIncrementSecondFormConstant m N 1 c MA MH,
    actualIncrementSecondFormConstant_nonneg m N 1 hc hMA hMH⟩
  have hQL : LipschitzOnWith K (actualNormalHessianInChart F e) O := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hQ.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) _ hConv
    intro z hz
    change ‖fderiv ℝ (actualNormalHessianInChart F e) z‖ ≤
      actualIncrementSecondFormConstant m N 1 c MA MH
    have hb := hQj 1 le_rfl z hz
    change 1^1 * ‖iteratedFDeriv ℝ 1 (actualNormalHessianInChart F e) z‖ ≤
      actualIncrementSecondFormConstant m N 1 c MA MH at hb
    simpa only [one_pow, one_mul, norm_iteratedFDeriv_one] using hb
  have hBL := (actualHessianLift (E := D) (F := V)).lipschitzWith.lipschitzOnWith.comp
    hQL (mapsTo_univ _ _)
  exact hBL.prodMk (Convex.lipschitzOnWith_of_nnnorm_fderiv_le hA hAT hConv)

/-- The original map jets through spatial order three now supply the local
uniform template radius. No derivative bound for the normal projection or
second form is an input. The original target tensor is used unchanged. -/
theorem round4_actual_template_from_map_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (c MA MH : ℝ) (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (MT : ℝ≥0)
    (hA : ∀ z ∈ O, DifferentiableAt ℝ A z)
    (hAT : ∀ z ∈ O, ‖fderiv ℝ A z‖₊ ≤ MT)
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu cT H : ℝ) (hmu : 0 < mu) (hcT : 0 < cT)
    (x : X) (hx : x ∈ O)
    (hfx : (round4ActualPhaseOperatorInChart F e x, A x) ∈
      actualAllowedPhaseTensorData D V R mu cT H) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu cT H hmu hcT
    let L := round4ActualTemplateFieldLipschitz m N c MA MH hc hMA hMH MT
    let rho := round4UniformTemplateRadius D V hdim R mu cT H hmu hcT / ((L : ℝ) + 1)
    0 < rho ∧ ∃ i : C.indices, ∀ y ∈ O ∩ ball x rho,
      round4ActualPhaseOperatorInChart F e y ∈ (C.template i).operatorDomain ∧
      A y ∈ (C.template i).tensorDomain := by
  exact round4_uniform_template_on_lipschitz_neighborhood D V hdim R mu cT H hmu hcT
    (fun z => (round4ActualPhaseOperatorInChart F e z, A z)) O
    (round4ActualTemplateFieldLipschitz m N c MA MH hc hMA hMH MT)
    (round4_actual_template_field_lipschitz F hF e he O hO hConv hcoord hJoint
      c MA MH hc hMA hMH hreserve hAj hHj A MT hA hAT) x hx hfx

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_phase_operator_original_rows
#print axioms GlobalEmbedding.Continuation.round4_actual_template_from_map_jets
