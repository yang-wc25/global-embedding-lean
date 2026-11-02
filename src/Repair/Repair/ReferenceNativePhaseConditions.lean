import Repair.ReferenceSlicePhases
import Repair.ReferenceWeightedNativeData

/-!
# All original native phase conditions from the fixed template hierarchy

This constructor produces primary, doubled and both signed interaction
conditions of the actual reweighted native datum.  The raw phases are the
literal host-linear phases, and the only pointwise geometric inputs are
the actual template membership and original transition derivative bounds.
The compact parameter manifold is arbitrary.  Interactions are checked on
the original relative joint supports and every orientation is handled.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance referenceNativeRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance referenceNativeSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,D)
private local instance referenceNativeTangentNormed (x : M) : NormedAddCommGroup (TangentSpace I x) := inferInstance
private local instance referenceNativeTangentSpace (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance
private local instance referenceNativeTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace I x) := inferInstance

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
    EuclideanSpace ℝ (Fin N)) ×
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

theorem repair_reference_native_phase_conditions
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ)
    (hT : 0 ≤ transitionBound)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (host : Fin Data.primaryCount → OpenPartialHomeomorph M D)
    (hhost : ∀ nu, host nu ∈ IsManifold.maximalAtlas I ∞ M)
    (index : Fin Data.primaryCount → C.indices)
    (edge : Fin Data.primaryCount → EdgePair (Module.finrank ℝ D+1))
    (label : Fin Data.primaryCount → ℕ)
    (hphase : ∀ nu, Data.phase nu = fun z => ((C.template (index nu)).covectors (edge nu)) (host nu z.2))
    (hsource : ∀ nu z, z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data →
      z.2 ∈ (host nu).source)
    (hoperator : ∀ nu z, z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data →
      ‖repairReferenceSliceOperator (fun x => Data.F (z.1,x)) (host nu) (host nu z.2)‖ ≤ R ∧
      repairReferenceSliceOperator (fun x => Data.F (z.1,x)) (host nu) (host nu z.2) ∈
        (C.template (index nu)).operatorDomain)
    (hlabel : ∀ nu mu, nu ≠ mu → ∀ z,
      z ∈ incrementsOriginalRelativeCutoffSupport Data nu ∩
        incrementsOriginalRelativeCutoffSupport Data mu → label nu ≠ label mu)
    (htransition : ∀ nu mu z,
      z ∈ incrementsOriginalRelativeCutoffSupport Data nu ∩
        incrementsOriginalRelativeCutoffSupport Data mu →
      ‖fderiv ℝ (host mu ∘ (host nu).symm) (host nu z.2)‖ ≤ transitionBound) :
    let weight := fun nu => repairReferenceSignedHierarchy C R transitionBound ^ label nu
    IncrementsOriginalPhaseConditions (repairReferenceWeightedData Data weight)
      (repairReferenceWeightedDomain Data weight hd) (repairReferenceWeightedSmooth Data weight hs) := by
  intro weight
  let E := repairReferenceWeightedData Data weight
  let hdE := repairReferenceWeightedDomain Data weight hd
  let hsE := repairReferenceWeightedSmooth Data weight hs
  have hw (nu : Fin Data.primaryCount) : weight nu ≠ 0 :=
    pow_ne_zero _ (zero_lt_one.trans (repairReferenceSignedHierarchy_gt_one C R transitionBound hT)).ne'
  have hraw (nu : Fin Data.primaryCount) (z : P × M)
      (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
      incrementsOriginalPhaseCovector Data nu z.1 z.2 =
        ((C.template (index nu)).covectors (edge nu)).comp (mfderiv I I (host nu) z.2) := by
    unfold incrementsOriginalPhaseCovector
    rw [hphase nu]
    exact repair_reference_source_linear_covector (host nu) (hhost nu) _ z.2 (hsource nu z hz)
  have hcov (nu : Fin Data.primaryCount) (z : P × M)
      (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
      incrementsOriginalPhaseCovector E nu z.1 z.2 =
        weight nu • ((C.template (index nu)).covectors (edge nu)).comp (mfderiv I I (host nu) z.2) := by
    rw [repair_reference_weighted_covector Data weight hd hs nu z hz,hraw nu z hz]
  have hprimary (nu : Fin Data.primaryCount) (z : P × M)
      (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
      GoodCovector (fun x => Data.F (z.1,x)) (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1)
        z.2 (incrementsOriginalPhaseCovector E nu z.1 z.2) := by
    rw [hcov nu z hz]
    exact (good_covector_smul_iff _ _ _ _ _ (hw nu)).mpr
      (repair_reference_slice_template_good C _ (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1)
        (host nu) (hhost nu) z.2 (hsource nu z hz) (index nu) (hoperator nu z hz).2 (edge nu))
  refine ⟨hprimary,?_,?_⟩
  · intro nu z hz
    exact (good_covector_smul_iff _ _ _ _ 2 (by norm_num)).mpr (hprimary nu z hz)
  · intro nu mu hne sign z hz
    have hnu : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local nu hz.1,incrementsOriginalRelativeCutoffSupport_subset Data nu hz.1⟩
    have hmu : z ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local mu hz.2,incrementsOriginalRelativeCutoffSupport_subset Data mu hz.2⟩
    have hf := incrementsOriginal_slice_contMDiff Data hd hs z.1 hnu.2.1
    have ordered (left right : Fin Data.primaryCount)
        (hleft : z ∈ Data.primaryDomain left ∩ incrementsOriginalParameterRegion Data)
        (hright : z ∈ Data.primaryDomain right ∩ incrementsOriginalParameterRegion Data)
        (hoverlap : z ∈ incrementsOriginalRelativeCutoffSupport Data left ∩
          incrementsOriginalRelativeCutoffSupport Data right)
        (horder : label right < label left) :
        GoodCovector (fun x => Data.F (z.1,x)) hf z.2
          (incrementsOriginalPhaseCovector E left z.1 z.2+incrementsOriginalPhaseCovector E right z.1 z.2) ∧
        GoodCovector (fun x => Data.F (z.1,x)) hf z.2
          (incrementsOriginalPhaseCovector E left z.1 z.2-incrementsOriginalPhaseCovector E right z.1 z.2) := by
      rw [hcov left z hleft,hcov right z hright]
      exact repair_reference_slice_signed_good C R transitionBound hT _ hf
        (host left) (host right) (hhost left) (hhost right) z.2
        (hsource left z hleft) (hsource right z hright) (index left) (index right)
        (hoperator left z hleft).1 (hoperator left z hleft).2 (edge left) (edge right)
        (htransition left right z hoverlap) horder
    have hpair :
        GoodCovector (fun x => Data.F (z.1,x)) hf z.2
          (incrementsOriginalPhaseCovector E nu z.1 z.2+incrementsOriginalPhaseCovector E mu z.1 z.2) ∧
        GoodCovector (fun x => Data.F (z.1,x)) hf z.2
          (incrementsOriginalPhaseCovector E nu z.1 z.2-incrementsOriginalPhaseCovector E mu z.1 z.2) := by
      rcases lt_or_gt_of_ne (hlabel nu mu hne z hz) with hlt | hgt
      · have hp := ordered mu nu hmu hnu ⟨hz.2,hz.1⟩ hlt
        refine ⟨by simpa only [add_comm] using hp.1,?_⟩
        have hn := (good_covector_smul_iff _ _ _ _ (-1 : ℝ) (by norm_num)).mpr hp.2
        have he : (-1 : ℝ) • (incrementsOriginalPhaseCovector E mu z.1 z.2-
            incrementsOriginalPhaseCovector E nu z.1 z.2) =
            incrementsOriginalPhaseCovector E nu z.1 z.2-incrementsOriginalPhaseCovector E mu z.1 z.2 := by
          ext v
          simp
        rwa [he] at hn
      · exact ordered nu mu hnu hmu hz hgt
    cases sign with
    | false =>
      have hNeg : (-1 : ℝ) • incrementsOriginalPhaseCovector E mu z.1 z.2 =
          -incrementsOriginalPhaseCovector E mu z.1 z.2 := by
        ext v
        simp
      change GoodCovector (fun x => Data.F (z.1,x)) hf z.2
        (incrementsOriginalPhaseCovector E nu z.1 z.2+(-1 : ℝ) • incrementsOriginalPhaseCovector E mu z.1 z.2)
      simpa only [hNeg,sub_eq_add_neg] using hpair.2
    | true =>
      change GoodCovector (fun x => Data.F (z.1,x)) hf z.2
        (incrementsOriginalPhaseCovector E nu z.1 z.2+(1 : ℝ) • incrementsOriginalPhaseCovector E mu z.1 z.2)
      simpa only [one_smul] using hpair.1

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_native_phase_conditions
