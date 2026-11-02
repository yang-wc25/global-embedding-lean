import Repair.IncrementLiteralSignedDifferential
import Repair.IncrementSignedNormalization

/-! Numerical noncritical and original Sym² reserves for the literal
physical signed phases in any observing host. The hierarchy, actual
transition and template membership generate all normalization data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance literalReserveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance literalReserveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

private theorem literal_reserve_of_normalized
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hxObs : x ∈ observer.source) (hxOwn : x ∈ owner.source)
    (phase : M → ℝ) (hPhase : DifferentiableAt ℝ (phase ∘ owner.symm) (owner x))
    (hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner x)‖ ≤ T)
    (index : C.indices) (edge : EdgePair (Module.finrank ℝ D+1))
    (hUpper : ‖repairReferenceSliceOperator F owner (owner x)‖ ≤ R)
    (hTemplate : repairReferenceSliceOperator F owner (owner x) ∈ (C.template index).operatorDomain)
    (c : ℝ) (hc : 1 ≤ |c|)
    (hClose : ‖c⁻¹ • fderiv ℝ (phase ∘ owner.symm) (owner x)-(C.template index).covectors edge‖ <
      incrementUniformSignedRadius C R) :
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (phase ∘ observer.symm) (observer x)‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
        (fderiv ℝ (phase ∘ observer.symm) (observer x)) v‖ := by
  have hz : (0,observer x) ∈ (repairReferenceHostTransition (Ep := ℝ) observer owner).source := by
    refine ⟨mem_univ _,observer.map_source hxObs,?_⟩
    change observer.symm (observer x) ∈ owner.source
    rwa [observer.left_inv hxObs]
  have h := increment_actual_signed_observing_host_reserves C R T hT
    (fun (_ : ℝ) => F) (fun _ => hF) observer owner hObserver hOwner
    (univ ×ˢ owner.target) (isOpen_univ.prod owner.open_target)
    (repair_reference_slice_joint_smooth F hF owner hOwner)
    (fun z : ℝ × M => phase z.2) (0,observer x) hz
    (by exact ⟨mem_univ _,by simpa only [repairReferenceHostTransition,OpenPartialHomeomorph.prod_apply,
      OpenPartialHomeomorph.refl_apply,Function.comp_apply,OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.symm_symm,observer.left_inv hxObs] using owner.map_source hxOwn⟩)
    (by
      change DifferentiableAt ℝ (phase ∘ owner.symm) (owner (observer.symm (observer x)))
      rw [observer.left_inv hxObs]
      exact hPhase)
    (by simpa only [observer.left_inv hxObs] using hInverse)
    index edge
    (by simpa only [repairReferenceHostTransition,OpenPartialHomeomorph.prod_apply,
      OpenPartialHomeomorph.refl_apply,OpenPartialHomeomorph.trans_apply,Function.comp_apply,
      OpenPartialHomeomorph.symm_symm,observer.left_inv hxObs,repairReferenceSliceOperator,id_eq] using hUpper)
    (by simpa only [repairReferenceHostTransition,OpenPartialHomeomorph.prod_apply,
      OpenPartialHomeomorph.refl_apply,OpenPartialHomeomorph.trans_apply,Function.comp_apply,
      OpenPartialHomeomorph.symm_symm,observer.left_inv hxObs,repairReferenceSliceOperator,id_eq] using hTemplate)
    c hc (by
      change ‖c⁻¹ • fderiv ℝ (phase ∘ owner.symm) (owner (observer.symm (observer x)))-
        (C.template index).covectors edge‖ < incrementUniformSignedRadius C R
      rw [observer.left_inv hxObs]
      exact hClose)
  exact h

theorem increment_literal_ordered_signed_reserves
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (observer left right : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hLeft : left ∈ IsManifold.maximalAtlas I ∞ M)
    (hRight : right ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hxObs : x ∈ observer.source) (hxLeft : x ∈ left.source) (hxRight : x ∈ right.source)
    (leftIndex rightIndex : C.indices)
    (leftEdge rightEdge : EdgePair (Module.finrank ℝ D+1))
    (hUpper : ‖repairReferenceSliceOperator F left (left x)‖ ≤ R)
    (hTemplate : repairReferenceSliceOperator F left (left x) ∈ (C.template leftIndex).operatorDomain)
    (hTransition : ‖fderiv ℝ (right ∘ left.symm) (left x)‖ ≤ T)
    (hInverse : ‖fderiv ℝ (observer ∘ left.symm) (left x)‖ ≤ T)
    {i j : ℕ} (hij : i < j) (branch : Fin 4) :
    let w := repairReferenceSignedHierarchy C R T
    let phase := incrementLiteralSignedPhase left right ((C.template leftIndex).covectors leftEdge)
      ((C.template rightIndex).covectors rightEdge) (w^j) (w^i) branch
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (phase ∘ observer.symm) (observer x)‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
        (fderiv ℝ (phase ∘ observer.symm) (observer x)) v‖ := by
  intro w phase
  let xi := (C.template leftIndex).covectors leftEdge
  let eta := (C.template rightIndex).covectors rightEdge
  let A := fderiv ℝ (right ∘ left.symm) (left x)
  have hEta : ‖eta.comp A‖ ≤ C.covectorBound*T :=
    (eta.opNorm_comp_le A).trans (mul_le_mul ((C.bounds rightIndex).2.2.2.2 rightEdge)
      hTransition (norm_nonneg _) C.covectorBound_pos.le)
  obtain ⟨c,hc,hClose⟩ := increment_four_signed_normalization (incrementUniformSignedRadius C R)
    (C.covectorBound*T) (incrementUniformSignedRadius_pos C R)
    (mul_nonneg C.covectorBound_pos.le hT.le) (eta.comp A) xi hEta hij branch
  have hd := increment_literal_signed_differential left right hLeft hRight xi eta (w^j) (w^i)
    x hxLeft hxRight branch
  apply literal_reserve_of_normalized C R T hT F hF observer left hObserver hLeft x hxObs hxLeft
    phase hd.1 hInverse leftIndex leftEdge hUpper hTemplate c hc
  rw [hd.2]
  exact hClose


theorem increment_literal_signed_reserves
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (observer left right : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hLeft : left ∈ IsManifold.maximalAtlas I ∞ M)
    (hRight : right ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hxObs : x ∈ observer.source) (hxLeft : x ∈ left.source) (hxRight : x ∈ right.source)
    (leftIndex rightIndex : C.indices)
    (leftEdge rightEdge : EdgePair (Module.finrank ℝ D+1))
    (hUpperLeft : ‖repairReferenceSliceOperator F left (left x)‖ ≤ R)
    (hUpperRight : ‖repairReferenceSliceOperator F right (right x)‖ ≤ R)
    (hTemplateLeft : repairReferenceSliceOperator F left (left x) ∈ (C.template leftIndex).operatorDomain)
    (hTemplateRight : repairReferenceSliceOperator F right (right x) ∈ (C.template rightIndex).operatorDomain)
    (hLeftRight : ‖fderiv ℝ (right ∘ left.symm) (left x)‖ ≤ T)
    (hRightLeft : ‖fderiv ℝ (left ∘ right.symm) (right x)‖ ≤ T)
    (hObsLeft : ‖fderiv ℝ (observer ∘ left.symm) (left x)‖ ≤ T)
    (hObsRight : ‖fderiv ℝ (observer ∘ right.symm) (right x)‖ ≤ T)
    (leftLabel rightLabel : ℕ) (hne : leftLabel ≠ rightLabel) (branch : Fin 4) :
    let w := repairReferenceSignedHierarchy C R T
    let phase := incrementLiteralSignedPhase left right ((C.template leftIndex).covectors leftEdge)
      ((C.template rightIndex).covectors rightEdge) (w^leftLabel) (w^rightLabel) branch
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (phase ∘ observer.symm) (observer x)‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
        (fderiv ℝ (phase ∘ observer.symm) (observer x)) v‖ := by
  intro w phase
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he := increment_literal_signed_swap left right ((C.template leftIndex).covectors leftEdge)
      ((C.template rightIndex).covectors rightEdge) (w^leftLabel) (w^rightLabel) branch
    let Q (f : M → ℝ) : Prop :=
      (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (f ∘ observer.symm) (observer x)‖ ∧
      ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
        ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
          (fderiv ℝ (f ∘ observer.symm) (observer x)) v‖
    have hout := increment_literal_ordered_signed_reserves C R T hT F hF observer right left hObserver hRight hLeft
      x hxObs hxRight hxLeft rightIndex leftIndex rightEdge leftEdge hUpperRight hTemplateRight
      hRightLeft hObsRight hlt (![0,2,1,3] branch)
    exact (congrArg Q he).mpr hout
  · exact increment_literal_ordered_signed_reserves C R T hT F hF observer left right hObserver hLeft hRight
      x hxObs hxLeft hxRight leftIndex rightIndex leftEdge rightEdge hUpperLeft hTemplateLeft
      hLeftRight hObsLeft hgt branch

theorem increment_literal_doubled_reserves
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hxObs : x ∈ observer.source) (hxOwn : x ∈ owner.source)
    (index : C.indices) (edge : EdgePair (Module.finrank ℝ D+1))
    (hUpper : ‖repairReferenceSliceOperator F owner (owner x)‖ ≤ R)
    (hTemplate : repairReferenceSliceOperator F owner (owner x) ∈ (C.template index).operatorDomain)
    (hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner x)‖ ≤ T)
    (label : ℕ) (branch : Fin 4) (hbranch : branch=0 ∨ branch=3) :
    let w := repairReferenceSignedHierarchy C R T
    let phase := incrementLiteralSignedPhase owner owner ((C.template index).covectors edge)
      ((C.template index).covectors edge) (w^label) (w^label) branch
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (phase ∘ observer.symm) (observer x)‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (repairReferenceSliceOperator F observer (observer x))
        (fderiv ℝ (phase ∘ observer.symm) (observer x)) v‖ := by
  intro w phase
  let xi := (C.template index).covectors edge
  have he : owner ∘ owner.symm =ᶠ[𝓝 (owner x)] id := by
    filter_upwards [owner.open_target.mem_nhds (owner.map_source hxOwn)] with y hy
    exact owner.right_inv hy
  have hid : fderiv ℝ (owner ∘ owner.symm) (owner x) = ContinuousLinearMap.id ℝ D := by
    rw [he.fderiv_eq,fderiv_id]
  have hw : 1 ≤ w^label := one_le_pow₀ (repairReferenceSignedHierarchy_gt_one C R T hT.le).le
  obtain ⟨c,hc,hclose⟩ := increment_doubled_normalization (incrementUniformSignedRadius C R) (w^label)
    (incrementUniformSignedRadius_pos C R) hw xi branch hbranch
  have hd := increment_literal_signed_differential owner owner hOwner hOwner xi xi (w^label) (w^label)
    x hxOwn hxOwn branch
  apply literal_reserve_of_normalized C R T hT F hF observer owner hObserver hOwner x hxObs hxOwn
    phase hd.1 hInverse index edge hUpper hTemplate c hc
  rw [hd.2,hid,ContinuousLinearMap.comp_id]
  exact hclose

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_literal_ordered_signed_reserves

#print axioms GlobalEmbedding.Continuation.increment_literal_signed_reserves
#print axioms GlobalEmbedding.Continuation.increment_literal_doubled_reserves
