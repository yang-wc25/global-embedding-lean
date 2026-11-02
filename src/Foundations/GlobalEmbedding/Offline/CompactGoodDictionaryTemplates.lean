import GlobalEmbedding.Offline.GoodDictionaryReserves
import GlobalEmbedding.Offline.JointGoodCovectorOpen
import GlobalEmbedding.Offline.UniformHierarchicalGoodPhases
import GlobalEmbedding.Offline.BestPhaseLipschitz
import GlobalEmbedding.Offline.CompactPositiveTensors
import Mathlib.Topology.Compactness.Compact

/-!
# Finite actual good-dictionary templates over compact operator/tensor data

Source: `main.tex` 695–696, compact allowed two-jets in
`repair-phase-preparation`.  The compact set here consists of actual fixed-target
second-form operators and actual source bilinear tensors.  Each local dictionary
is constructed by `positive_good_dictionary_with_operator_tensor_reserves`.
Native compactness extracts a finite open cover; finite positive minima and
finite maxima provide common reserves without any chart-count factor.

`ActualGoodDictionaryTemplate` is only a record of those actual maps and their
proved identities.  It is not a replacement tensor, metric, kernel, or good
predicate.  Compactness of the geometric allowed two-jet image remains an input
to this compact-data consumer, rather than being inferred from arbitrary buffers.
-/

noncomputable section

open GlobalEmbedding.Paper Set
open scoped TensorProduct ContDiff Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance templateSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance templateSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable local instance templateBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

private noncomputable local instance templateBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance templateBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- A finite positive family has a common strictly positive lower bound. An
extra value one handles the empty family without a nonempty-index assumption. -/
theorem finite_positive_common_lower_bound {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ b i := by
  let b' : Option ι → ℝ := fun i ↦ i.elim 1 b
  let hne : (Finset.univ : Finset (Option ι)).Nonempty := ⟨none, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne b', ?_, ?_⟩
  · apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => norm_num [b']
    | some i => exact hb i
  · intro i
    exact Finset.inf'_le b' (Finset.mem_univ (some i))

/-- A full local template made of the actual original covectors, native forms,
and genuine open operator/tensor domains. All properties are proof fields of
the constructed data, never assumptions in the compact existence theorem. -/
structure ActualGoodDictionaryTemplate where
  covectors : EdgePair (Module.finrank ℝ E + 1) → E →L[ℝ] ℝ
  coefficients : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
    (EdgePair (Module.finrank ℝ E + 1) → ℝ)
  operatorDomain : Set (SymmetricSquare E →L[ℝ] F)
  tensorDomain : Set (E →L[ℝ] E →L[ℝ] ℝ)
  restrictionReserve : ℝ
  coefficientReserve : ℝ
  covectorRadius : ℝ
  restrictionReserve_pos : 0 < restrictionReserve
  coefficientReserve_pos : 0 < coefficientReserve
  covectorRadius_pos : 0 < covectorRadius
  isOpen_operatorDomain : IsOpen operatorDomain
  isOpen_tensorDomain : IsOpen tensorDomain
  covectors_ne_zero : ∀ i, covectors i ≠ 0
  independent : LinearIndependent ℝ (fun i ↦ (covectors i).smulRight (covectors i))
  coefficient_left_inverse : ∀ a, coefficients (continuousRankOneReconstruct covectors a) = a
  coefficient_right_inverse : ∀ A, (∀ v w, A v w = A w v) →
    continuousRankOneReconstruct covectors (coefficients A) = A
  operator_control : ∀ B ∈ operatorDomain, ∀ i,
    LinearSecondFormGoodCovector B.toLinearMap (covectors i).toLinearMap ∧
    (∀ z, restrictionReserve * ‖z‖ ≤ ‖covectorRestriction B (covectors i) z‖) ∧
    ∃ e : SymmetricSquare (covectors i).ker ≃L[ℝ]
        LinearMap.range (covectorRestriction B (covectors i)).toLinearMap,
      (∀ z, (e z).val = covectorRestriction B (covectors i) z) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ restrictionReserve⁻¹
  covector_ball_control : ∀ B ∈ operatorDomain, ∀ i (η : E →L[ℝ] ℝ),
    ‖η - covectors i‖ < covectorRadius →
      LinearSecondFormGoodCovector B.toLinearMap η.toLinearMap
  coefficient_control : ∀ A ∈ tensorDomain, ∀ i, coefficientReserve ≤ coefficients A i
  amplitudes_smooth : ∀ i, ContDiffOn ℝ ∞ (fun A ↦ Real.sqrt (coefficients A i)) tensorDomain
  amplitudes_reconstruct : ∀ A ∈ tensorDomain, (∀ v w, A v w = A w v) →
    continuousRankOneReconstruct covectors (fun i ↦ (Real.sqrt (coefficients A i)) ^ 2) = A

variable {E F}

/-- A phase-regular actual second form and a positive source tensor lie in
one constructed full template. No local dictionary or reserve is an input. -/
theorem exists_actual_good_dictionary_template
    (B : SymmetricSquare E →L[ℝ] F)
    (hphase : ∃ ξ : E →L[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ.toLinearMap)
    (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hgsymm : ∀ v w, g v w = g w v) (hgpos : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ T : ActualGoodDictionaryTemplate E F, B ∈ T.operatorDomain ∧ g ∈ T.tensorDomain := by
  obtain ⟨ξ, D, μ, c, L, U, V, hμ, hc, _hL, hU, hBU, hV, hgV, _hcard,
      hne, hLI, hleft, hright, _hDL, _hop, hoperator, hcoeff, hsmooth, hrec⟩ :=
    positive_good_dictionary_with_operator_tensor_reserves B hphase g hgsymm hgpos
  have hlocal (i : EdgePair (Module.finrank ℝ E + 1)) :=
    actual_good_covector_product_ball B (ξ i) (hoperator B hBU i).1
  choose ε hε W hW hBW hball using hlocal
  obtain ⟨ε0, hε0, hεle⟩ := finite_positive_common_lower_bound ε hε
  let O := U ∩ ⋂ i, W i
  have hO : IsOpen O := hU.inter (isOpen_iInter_of_finite hW)
  have hBO : B ∈ O := ⟨hBU, Set.mem_iInter.mpr hBW⟩
  exact ⟨{
    covectors := ξ
    coefficients := D
    operatorDomain := O
    tensorDomain := V
    restrictionReserve := μ
    coefficientReserve := c
    covectorRadius := ε0
    restrictionReserve_pos := hμ
    coefficientReserve_pos := hc
    covectorRadius_pos := hε0
    isOpen_operatorDomain := hO
    isOpen_tensorDomain := hV
    covectors_ne_zero := hne
    independent := hLI
    coefficient_left_inverse := hleft
    coefficient_right_inverse := hright
    operator_control := fun A hA ↦ hoperator A hA.1
    covector_ball_control := fun A hA i η hη ↦
      hball i A (Set.mem_iInter.mp hA.2 i) η (lt_of_lt_of_le hη (hεle i))
    coefficient_control := hcoeff
    amplitudes_smooth := hsmooth
    amplitudes_reconstruct := hrec }, hBO, hgV⟩

/-- Native compactness produces a finite cover by full actual good dictionary
templates, including the empty compact set. Each selected template is attached
to one actual point of the same compact operator/tensor data set. -/
theorem compact_actual_good_dictionary_template_cover
    (K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ)))
    (hK : IsCompact K)
    (hphase : ∀ z ∈ K, ∃ ξ : E →L[ℝ] ℝ,
      LinearSecondFormGoodCovector z.1.toLinearMap ξ.toLinearMap)
    (hsymm : ∀ z ∈ K, ∀ v w, z.2 v w = z.2 w v)
    (hpos : ∀ z ∈ K, ∀ v, v ≠ 0 → 0 < z.2 v v) :
    ∃ (s : Finset K) (T : s → ActualGoodDictionaryTemplate E F),
      (∀ i : s, i.val.val.1 ∈ (T i).operatorDomain ∧ i.val.val.2 ∈ (T i).tensorDomain) ∧
      ∀ z ∈ K, ∃ i : s, z.1 ∈ (T i).operatorDomain ∧ z.2 ∈ (T i).tensorDomain := by
  classical
  have hlocal (z : K) : ∃ T : ActualGoodDictionaryTemplate E F,
      z.val.1 ∈ T.operatorDomain ∧ z.val.2 ∈ T.tensorDomain :=
    exists_actual_good_dictionary_template z.val.1 (hphase z.val z.property) z.val.2
      (hsymm z.val z.property) (hpos z.val z.property)
  choose T hT using hlocal
  let O (z : K) := (T z).operatorDomain ×ˢ (T z).tensorDomain
  have hO (z : K) : IsOpen (O z) :=
    (T z).isOpen_operatorDomain.prod (T z).isOpen_tensorDomain
  have hcover : K ⊆ ⋃ z : K, O z := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hT ⟨z, hz⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO hcover
  refine ⟨s, fun i ↦ T i.val, ?_, ?_⟩
  · intro i
    exact hT i.val
  · intro z hz
    obtain ⟨i, hi, hzO⟩ := Set.mem_iUnion₂.mp (hs hz)
    exact ⟨⟨i, hi⟩, hzO⟩

/-- A native finite maximum bounds a finite family in its actual norm. The
additional one makes the bound positive even for the empty family. -/
theorem finite_norm_common_upper_bound {ι X : Type*} [Fintype ι]
    [SeminormedAddCommGroup X] (f : ι → X) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, ‖f i‖ ≤ M := by
  classical
  let B : NNReal := Finset.univ.sup (fun i ↦ ‖f i‖₊)
  let M : ℝ := (B : ℝ) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro i
  have hi : ‖f i‖₊ ≤ B :=
    Finset.le_sup (f := fun j ↦ ‖f j‖₊) (Finset.mem_univ i)
  exact (show ‖f i‖ ≤ (B : ℝ) from hi).trans
    (le_add_of_nonneg_right zero_le_one)

/-- Finite actual templates with common positive reserves and native norm
bounds. This record only packages proved data of the previous template record;
the compact existence theorem constructs every field, including all bounds. -/
structure UniformActualGoodDictionaryCover
    (K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ))) where
  indices : Finset K
  template : indices → ActualGoodDictionaryTemplate E F
  centers : ∀ i, i.val.val.1 ∈ (template i).operatorDomain ∧
    i.val.val.2 ∈ (template i).tensorDomain
  covers : ∀ z ∈ K, ∃ i, z.1 ∈ (template i).operatorDomain ∧
    z.2 ∈ (template i).tensorDomain
  restrictionReserve : ℝ
  coefficientReserve : ℝ
  covectorRadius : ℝ
  coefficientBound : ℝ
  covectorBound : ℝ
  restrictionReserve_pos : 0 < restrictionReserve
  coefficientReserve_pos : 0 < coefficientReserve
  covectorRadius_pos : 0 < covectorRadius
  coefficientBound_pos : 0 < coefficientBound
  covectorBound_pos : 0 < covectorBound
  bounds : ∀ i,
    restrictionReserve ≤ (template i).restrictionReserve ∧
    coefficientReserve ≤ (template i).coefficientReserve ∧
    covectorRadius ≤ (template i).covectorRadius ∧
    ‖(template i).coefficients‖ ≤ coefficientBound ∧
    ∀ a, ‖(template i).covectors a‖ ≤ covectorBound

/-- The actual compact data determine a finite full cover, common positive
kernel/coefficent/covector-ball reserves and native coefficient/covector norm
maxima. No positivity, bound, cover, or dictionary is supplied as extra data. -/
theorem compact_actual_good_dictionary_uniform_cover
    (K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ)))
    (hK : IsCompact K)
    (hphase : ∀ z ∈ K, ∃ ξ : E →L[ℝ] ℝ,
      LinearSecondFormGoodCovector z.1.toLinearMap ξ.toLinearMap)
    (hsymm : ∀ z ∈ K, ∀ v w, z.2 v w = z.2 w v)
    (hpos : ∀ z ∈ K, ∀ v, v ≠ 0 → 0 < z.2 v v) :
    Nonempty (UniformActualGoodDictionaryCover (E := E) (F := F) K) := by
  classical
  obtain ⟨s, T, hcenters, hcover⟩ :=
    compact_actual_good_dictionary_template_cover K hK hphase hsymm hpos
  obtain ⟨μ, hμ, hμle⟩ := finite_positive_common_lower_bound
    (fun i : s ↦ (T i).restrictionReserve) (fun i ↦ (T i).restrictionReserve_pos)
  obtain ⟨c, hc, hcle⟩ := finite_positive_common_lower_bound
    (fun i : s ↦ (T i).coefficientReserve) (fun i ↦ (T i).coefficientReserve_pos)
  obtain ⟨ε, hε, hεle⟩ := finite_positive_common_lower_bound
    (fun i : s ↦ (T i).covectorRadius) (fun i ↦ (T i).covectorRadius_pos)
  obtain ⟨L, hL, hLle⟩ := finite_norm_common_upper_bound (fun i : s ↦ (T i).coefficients)
  obtain ⟨M, hM, hMle⟩ := finite_norm_common_upper_bound
    (fun i : s × EdgePair (Module.finrank ℝ E + 1) ↦ (T i.1).covectors i.2)
  exact ⟨{
    indices := s, template := T, centers := hcenters, covers := hcover
    restrictionReserve := μ, coefficientReserve := c, covectorRadius := ε
    coefficientBound := L, covectorBound := M
    restrictionReserve_pos := hμ, coefficientReserve_pos := hc, covectorRadius_pos := hε
    coefficientBound_pos := hL, covectorBound_pos := hM
    bounds := fun i ↦ ⟨hμle i, hcle i, hεle i, hLle i, fun a ↦ hMle (i, a)⟩ }⟩

/-- The common radius is valid for the actual good condition at every operator
in every selected template domain. -/
theorem UniformActualGoodDictionaryCover.covector_ball_control
    {K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (B : SymmetricSquare E →L[ℝ] F) (hB : B ∈ (C.template i).operatorDomain)
    (a : EdgePair (Module.finrank ℝ E + 1)) (η : E →L[ℝ] ℝ)
    (hη : ‖η - (C.template i).covectors a‖ < C.covectorRadius) :
    LinearSecondFormGoodCovector B.toLinearMap η.toLinearMap :=
  (C.template i).covector_ball_control B hB a η (hη.trans_le (C.bounds i).2.2.1)

/-- The common positive reserve bounds the same actual canonical Sym²-kernel
restriction and the inverse of its actual range equivalence in every template. -/
theorem UniformActualGoodDictionaryCover.operator_control
    {K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (B : SymmetricSquare E →L[ℝ] F) (hB : B ∈ (C.template i).operatorDomain)
    (a : EdgePair (Module.finrank ℝ E + 1)) :
    LinearSecondFormGoodCovector B.toLinearMap ((C.template i).covectors a).toLinearMap ∧
    (∀ z, C.restrictionReserve * ‖z‖ ≤
      ‖covectorRestriction B ((C.template i).covectors a) z‖) ∧
    ∃ e : SymmetricSquare ((C.template i).covectors a).ker ≃L[ℝ]
        LinearMap.range (covectorRestriction B ((C.template i).covectors a)).toLinearMap,
      (∀ z, (e z).val = covectorRestriction B ((C.template i).covectors a) z) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ C.restrictionReserve⁻¹ := by
  obtain ⟨hgood, hlower, e, he, hinv⟩ := (C.template i).operator_control B hB a
  refine ⟨hgood, ?_, e, he, ?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg z)).trans (hlower z)
  · exact hinv.trans ((inv_le_inv₀ (C.template i).restrictionReserve_pos
      C.restrictionReserve_pos).mpr (C.bounds i).1)

/-- Every actual tensor in a selected template has the same common positive
coefficient floor, while its actual coefficient vector obeys the common
operator-norm bound. The original tensor reconstruction remains exact. -/
theorem UniformActualGoodDictionaryCover.coefficient_control
    {K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hg : g ∈ (C.template i).tensorDomain)
    (hsymm : ∀ v w, g v w = g w v) :
    (∀ a, C.coefficientReserve ≤ (C.template i).coefficients g a) ∧
    ‖(C.template i).coefficients g‖ ≤ C.coefficientBound * ‖g‖ ∧
    continuousRankOneReconstruct (C.template i).covectors
      (fun a ↦ (Real.sqrt ((C.template i).coefficients g a)) ^ 2) = g := by
  refine ⟨fun a ↦ (C.bounds i).2.1.trans ((C.template i).coefficient_control g hg a),
    ?_, (C.template i).amplitudes_reconstruct g hg hsymm⟩
  exact ((C.template i).coefficients.le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (C.bounds i).2.2.2.1 (norm_nonneg g))

/-- A single hierarchy weight from the compact data works for arbitrary labels
and arbitrary selections of covectors from templates whose operator domains
contain the same actual second form. Its definition has no chart-count input. -/
theorem UniformActualGoodDictionaryCover.labeled_interactions_good
    {K : Set ((SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) {ι : Type*}
    (B : SymmetricSquare E →L[ℝ] F) (t : ι → C.indices)
    (a : ι → EdgePair (Module.finrank ℝ E + 1)) (label : ι → ℕ)
    (hB : ∀ j, B ∈ (C.template (t j)).operatorDomain) :
    let Λ := hierarchicalGoodWeight C.covectorRadius C.covectorBound
    (∀ j, LinearSecondFormGoodCovector B.toLinearMap
      (Λ ^ label j • (C.template (t j)).covectors (a j)).toLinearMap) ∧
    (∀ j, LinearSecondFormGoodCovector B.toLinearMap
      ((2 : ℝ) • (Λ ^ label j • (C.template (t j)).covectors (a j))).toLinearMap) ∧
    ∀ j k, label j ≠ label k →
      LinearSecondFormGoodCovector B.toLinearMap
        (Λ ^ label j • (C.template (t j)).covectors (a j) +
          Λ ^ label k • (C.template (t k)).covectors (a k)).toLinearMap ∧
      LinearSecondFormGoodCovector B.toLinearMap
        (Λ ^ label j • (C.template (t j)).covectors (a j) -
          Λ ^ label k • (C.template (t k)).covectors (a k)).toLinearMap := by
  exact labeled_weighted_good_of_uniform_radius B.toLinearMap
    C.covectorRadius_pos C.covectorBound_pos.le
    (fun j ↦ (C.template (t j)).covectors (a j)) label
    (fun j ↦ (C.bounds (t j)).2.2.2.2 (a j))
    (fun j η hη ↦ C.covector_ball_control (t j) B (hB j) (a j) η hη)

/-- The bounded positive-margin operator class and bounded coercive source
tensors admit full uniform templates. Compactness and actual good witnesses
are proved from these numerical bounds, rather than assumed from the user. -/
theorem bounded_phase_tensor_uniform_templates [FiniteDimensional ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ E) (R m lam T : ℝ) (hm : 0 < m) (hlam : 0 < lam) :
    Nonempty (UniformActualGoodDictionaryCover
      ({B : SymmetricSquare E →L[ℝ] F | ‖B‖ ≤ R ∧ m ≤ bestPhaseSupremum B} ×ˢ
        boundedPositiveTensorSet E lam T)) := by
  apply compact_actual_good_dictionary_uniform_cover _
    ((bounded_phase_operator_set_compact hdim R m).prod
      (boundedPositiveTensorSet_isCompact lam T))
  · intro z hz
    obtain ⟨ξ, _hunit, hξ⟩ := actual_good_covector_of_positive_bestPhaseSupremum
      hdim z.1 (hm.trans_le hz.1.2)
    exact ⟨ξ, hξ⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact boundedPositiveTensorSet_posDef hlam hz.2

#print axioms exists_actual_good_dictionary_template
#print axioms finite_positive_common_lower_bound
#print axioms compact_actual_good_dictionary_template_cover
#print axioms finite_norm_common_upper_bound
#print axioms compact_actual_good_dictionary_uniform_cover
#print axioms UniformActualGoodDictionaryCover.covector_ball_control
#print axioms UniformActualGoodDictionaryCover.operator_control
#print axioms UniformActualGoodDictionaryCover.coefficient_control
#print axioms UniformActualGoodDictionaryCover.labeled_interactions_good
#print axioms bounded_phase_tensor_uniform_templates

end GlobalEmbedding.Offline
