import Repair.ReferenceOriginalLocalFactory
import Repair.ReferenceZeroExtendedCarrierData
import Repair.ReferenceProductColoring

/-!
# All actual host factories form one original native reference datum

The functions below retain the same finite local templates, square bumps,
normal carriers and real original product charts.  Global smoothness is
proved through zero extension.  Separate source/parameter colors give a
single bounded label for the actual original Fin-indexed primary family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance globalFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance globalFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance globalFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance globalFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance globalFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

variable (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : (Fin seed.atlas.count × Fin seed.parameterCount) →
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
  (center : (Fin seed.atlas.count × Fin seed.parameterCount) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))

include hF Htensor O K center in
def repairReferenceOriginalFamilyInner (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (q : (family i).s) : P × M → ℝ :=
  repairReferenceChartCutoff ((seed.parameterChart i.2).prod (seed.atlas.chart i.1))
    (round4RefinementSquareCutoff X (family i).s b.cutoffRadius q)

include hF Htensor O K center in
def repairReferenceOriginalFamilyData
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ) :
    IncrementsOriginalNativeData (m+1) d N M P :=
  repairOriginalZeroExtendedCarrierTemplateData
    (Host := Fin seed.atlas.count × Fin seed.parameterCount) (Piece := fun i => (family i).s) seed hF
    (fun i => seed.atlas.chart i.1) (fun i => hseed.atlas_smooth.chart_mem i.1)
    (fun i q => b.cover.template ((family i).pick q)) outer (fun i => seed.parameterChart i.2)
    (fun i q => round4RefinementSquareCutoff X (family i).s b.cutoffRadius q)
    (fun a => (family a.1).actualNormal a.2.1 a.2.2)

include hF Htensor O K center in
theorem repair_reference_factory_cutoff_compact
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (q : (family i).s) :
    IsCompact (tsupport (round4RefinementSquareCutoff X (family i).s b.cutoffRadius q)) := by
  have hs : tsupport (round4RefinementSquareCutoff X (family i).s b.cutoffRadius q) ⊆
      closedBall q.val (2*b.cutoffRadius) :=
    (tensorLocalNormalizedCutoff_tsupport_subset
      (fun z : (family i).s => actualRefinementBump X b.cutoffRadius z.val) q).trans
      (by rw [actualRefinementBump_tsupport X b.cutoffRadius b.cutoffRadius_pos q.val])
  exact (isCompact_closedBall q.val _).of_isClosed_subset (isClosed_tsupport _) hs

theorem repair_reference_original_native_joint_target
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (z : X)
    (hz : parameterTensorModelEquiv (m+1) d z ∈ S i) :
    z ∈ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target := by
  have h := hSO i hz
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z)=z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)=z.2 at hx
  exact ⟨by simpa only [hp] using h.2,by simpa only [hx] using h.1⟩

include hF Htensor O K center in
theorem repair_reference_factory_cutoff_target
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (q : (family i).s) :
    tsupport (round4RefinementSquareCutoff X (family i).s b.cutoffRadius q) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target := by
  let a0 : Edge := ⟨(⟨0,by omega⟩,⟨1,by have := b.templateDim; omega⟩),by change (0:ℕ)<1; omega⟩
  intro y hy
  have hO := ((family i).charts q a0).source_domain (((family i).normal_support q a0 hy).1)
  exact repair_reference_original_native_joint_target seed S hSO i y (hSample i y hO)

include hF Htensor O K center in
theorem repair_reference_original_family_admissibility
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ seed.F0)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i)) :
    let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      IncrementsOriginalFreeNormalConditions data hd hs := by
  intro data
  exact repair_original_zero_extended_carrier_admissibility
    (Host := Fin seed.atlas.count × Fin seed.parameterCount) (Piece := fun i => (family i).s)
    seed hseed hFjoint hF
    (fun i => seed.atlas.chart i.1) (fun i => hseed.atlas_smooth.chart_mem i.1)
    (fun i q => b.cover.template ((family i).pick q)) outer hOuter
    (fun i => seed.parameterChart i.2) (fun i => hseed.parameter_charts_smooth i.2)
    (fun i q => round4RefinementSquareCutoff X (family i).s b.cutoffRadius q)
    (fun i q => (family i).cutoff_smooth q)
    (repair_reference_factory_cutoff_compact b seed hF Htensor S O K center family)
    (repair_reference_factory_cutoff_target b seed hF Htensor S O K center family hSO hSample)
    (fun a => (family a.1).actualNormal a.2.1 a.2.2)
    (fun a => (family a.1).normal_support a.2.1 a.2.2)

include hF Htensor O K center in
/-- The exact original primary Fin indices receive labels bounded before
the seed and every source/parameter atlas count. -/
theorem repair_reference_original_family_labels
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (sourceSupport : Fin seed.atlas.count → Set M)
    (parameterSupport : Fin seed.parameterCount → Set P)
    (Ds Dp : ℕ)
    (hDs : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp)
    (hOuter : ∀ i, tsupport (outer i) ⊆ parameterSupport i.2 ×ˢ sourceSupport i.1) :
    let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    ∃ label : Fin data.primaryCount → ℕ,
      (∀ nu, label nu < ((Ds+2)*(Dp+2))*(b.pieceBound*Fintype.card Edge)) ∧
      ∀ nu mu, nu ≠ mu → (tsupport (data.cutoff nu) ∩ tsupport (data.cutoff mu)).Nonempty →
        label nu ≠ label mu := by
  intro data
  let Piece : (Fin seed.atlas.count × Fin seed.parameterCount) → Type :=
    fun i => ↥(family i).s
  let inner := repairReferenceOriginalFamilyInner b seed hF Htensor S O K center family
  let supp := fun a : (Σ i, Piece i × Edge) => tsupport (fun z => outer a.1 z*inner a.1 a.2.1 z)
  have hCard (i : Fin seed.atlas.count × Fin seed.parameterCount) : Fintype.card (Piece i) ≤ b.pieceBound := by
    simpa only [Piece,Fintype.card_coe] using (family i).card
  obtain ⟨label,hBound,hDistinct⟩ := repair_reference_product_template_labels sourceSupport parameterSupport
    Ds Dp b.pieceBound hDs hDp hCard supp
    (fun a => tsupport_mul_subset_left.trans (hOuter a.1))
  let e := repairTemplateIndex (m := m) (Piece := Piece)
  refine ⟨fun nu => label (e nu),fun nu => hBound (e nu),?_⟩
  intro nu mu hne hOverlap
  exact hDistinct (e nu) (e mu) (fun h => hne (e.injective h)) hOverlap

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_admissibility
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_labels
