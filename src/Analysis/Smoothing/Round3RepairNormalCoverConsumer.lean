import Smoothing.Round3RepairNormalStage
import Smoothing.Round3RepairStageSmoothTarget
import Smoothing.Round3RepairOriginalLocalSmooth
import Smoothing.Round3OuterStageIntrinsicNormalNorm

/-! A literal same-SF stage gets its actual intrinsic normal, all original
normal budgets, full original input smoothness and the true original normal
conditions.  The only remaining normal-side data are fixed charts and their
stable lower reserves.  New normal jets, normal regularity, unit length and
phase-free legality are conclusions of the actual projection construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
universe uA
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local notation "Y" => Fin (m+1+d) → ℝ

structure Round3RepairNormalRebound
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {r : ℕ} {budget : ℝ} {reference givenPacket : ℕ → ℝ}
    (old : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M)) (normalProfile : ℕ → ℝ) where
  stage : Round3RepairOriginalSmoothingStage (round3RepairRebindNormalData Data normal domain)
    BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference (fun j => max (givenPacket j) (normalProfile j))
  oldMap_eq : stage.oldMap = old.oldMap
  referenceMap_eq : stage.referenceMap = old.referenceMap
  metric_eq : stage.metric = old.metric
  delta_eq : stage.delta = old.delta
  deltaNext_eq : stage.deltaNext = old.deltaNext
  ell_eq : stage.ell = old.ell
  t_eq : stage.t = old.t
  domain_conditions : IncrementsOriginalDomainConditions (round3RepairRebindNormalData Data normal domain)
  smooth_inputs : IncrementsOriginalSmoothInputs (round3RepairRebindNormalData Data normal domain)
  normal_conditions : IncrementsOriginalFreeNormalConditions
    (round3RepairRebindNormalData Data normal domain) domain_conditions smooth_inputs

/-- The common original normal constant is selected before every current
map and every actual primary family.  Different primary labels and different
samples may use different actual adapted charts, with no cardinality factor. -/
theorem round3_exists_uniform_actual_normal_rebound_stage
    (BS0 TS0 BP0 TP0 T Tobs Mv : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hTobs : ∀ j, 0 ≤ Tobs j) (hMv : ∀ j, 0 ≤ Mv j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hDomain : ∀ ν, IsOpen (domain ν))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (hCover : ∀ ν, incrementsOriginalRelativeCutoffSupport Data ν ⊆ domain ν)
    (vref : Fin Data.primaryCount → P × M → Ey),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    let normal := fun ν => parameterRound2_intrinsicUnitFreeNormalField (fun p x => Data.F (p,x)) hF
      (fun p x => Data.phase ν (p,x)) (vref ν)
    let E := round3RepairRebindNormalData Data normal domain
    ∀ (A : Fin Data.primaryCount → Type uA)
      (cover : ∀ ν, Round3OriginalNormalCoverGeometry Data hF
        (fun p x => Data.phase ν (p,x)) (vref ν) (A ν)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation E ν) cF cT mu),
    (∀ ν z, z ∈ domain ν ∩ incrementsOriginalParameterRegion Data →
      ∃ i : Fin Data.atlas.count × Fin Data.parameterCount,
        z.1 ∈ (Data.parameterChart i.2).source ∧ z.2 ∈ (Data.atlas.chart i.1).source ∧
        ∃ a : A ν, parameterRound2_originalForwardCoordinates Data i z ∈ (cover ν).original i a) →
    (∀ ν i a k, 1 ≤ k → ∀ y ∈ incrementsOriginalPrimaryEvaluation E ν i ∩ (cover ν).original i a,
      ‖iteratedFDeriv ℝ k (round3OriginalAdaptedTransition Data.atlas
        ((cover ν).host i a).1 ((cover ν).chart i a)) ((cover ν).forward i a y)‖ ≤ T k) →
    (∀ ν i a k, 1 ≤ k → ∀ y ∈ incrementsOriginalPrimaryEvaluation E ν i ∩ (cover ν).original i a,
      ‖iteratedFDeriv ℝ k ((cover ν).forward i a) y‖ ≤ Tobs k) →
    (∀ ν i a k, ∀ y ∈ incrementsOriginalPrimaryEvaluation E ν i ∩ (cover ν).original i a,
      ‖iteratedFDeriv ℝ k (round3NormalChartReference Data ((cover ν).host i a)
        ((cover ν).chart i a) (vref ν)) ((cover ν).forward i a y)‖ ≤ Mv k) →
    (∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,ℝ) ∞ (Data.phase ν)
      (Data.primaryDomain ν ∩ incrementsOriginalParameterRegion Data)) →
    (∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,ℝ) ∞ (Data.cutoff ν)
      (Data.primaryDomain ν ∩ incrementsOriginalParameterRegion Data)) →
    Nonempty (Round3RepairNormalRebound stage normal domain C) := by
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_actual_stage_intrinsic_normal_original_norms
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 T Tobs Mv hBS0 hTS0 hBP0 hTP0 hT hTobs hMv
    Ds Dp radius hradius r budget cF cT mu hbudget hcF hcT hmu
  refine ⟨C,hC,?_⟩
  intro Data reference givenPacket stage hd domain hDomain hSub hCover vref hF normal E
    A cover hPhysical hChartJets hObserverJets hReferenceJets hPhase hCutoff
  have hActual (ν : Fin Data.primaryCount) := hMake Data reference givenPacket stage
    (fun p x => Data.phase ν (p,x)) (vref ν) (A ν)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
    (incrementsOriginalPrimaryEvaluation E ν)
    (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart)
    (cover ν) (hChartJets ν) (hObserverJets ν) (hReferenceJets ν)
  have hNormalSmooth (ν : Fin Data.primaryCount) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ (normal ν)
        (domain ν ∩ incrementsOriginalParameterRegion Data) := by
    intro z hz
    obtain ⟨i,hp,hx,a,ha⟩ := hPhysical ν z hz
    have hCoordinates := ((hActual ν).1 i).mono (subset_iUnion (fun a => (cover ν).original i a) a)
    exact (round3_repair_original_map_contMDiffAt_of_coordinate_germ Data hd (normal ν) i
      ((cover ν).original i a) ((cover ν).original_open i a) hCoordinates z hp hx ha).contMDiffWithinAt
  have hUnit (ν : Fin Data.primaryCount) (z : P × M)
      (hz : z ∈ domain ν ∩ incrementsOriginalParameterRegion Data) : ‖normal ν z‖ = 1 := by
    obtain ⟨i,hp,hx,a,ha⟩ := hPhysical ν z hz
    have hu := (hActual ν).2.1 i a _ ((cover ν).forward_maps i a ha)
    have he := (cover ν).same_point i a _ ha
    rw [he,parameterRound2_originalForward_left_inv Data i z hp hx] at hu
    exact hu
  have hProduced (j : ℕ) (ν : Fin Data.primaryCount) := (hActual ν).2.2.2 j
  let newStage := stage.rebindNormal normal domain hd.primary_open hDomain hSub C hC hProduced
  let newHd : IncrementsOriginalDomainConditions E :=
    round3_repair_rebind_domain Data normal domain hd hDomain hCover
  let newHs : IncrementsOriginalSmoothInputs E :=
    round3_repair_stage_original_smooth_inputs E BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference (fun j => max (givenPacket j) (C j))
      newStage
      (fun ν => (hPhase ν).mono (fun _ hz => ⟨hSub ν hz.1,hz.2⟩))
      (fun ν => (hCutoff ν).mono (fun _ hz => ⟨hSub ν hz.1,hz.2⟩)) hNormalSmooth
  have newHn : IncrementsOriginalFreeNormalConditions E newHd newHs := by
    refine ⟨hUnit,?_,?_⟩
    · intro ν z hz
      exact ((hActual ν).2.2.1 z).1
    · intro ν z hz u v
      exact ((hActual ν).2.2.1 z).2 u v
  exact ⟨⟨newStage,rfl,rfl,rfl,rfl,rfl,rfl,rfl,newHd,newHs,newHn⟩⟩


/-- In the genuine closed-parameter case, the normal consumer's physical
cover is produced by the original samples and native cover.  No larger norm
domain or extra neighborhood assumption is inserted. -/
theorem round3_repair_normal_physical_cover_of_closed_parameters
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hK : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (normal vref : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (A : Fin Data.primaryCount → Type uA) (cF cT mu : ℝ)
    (cover : ∀ ν, Round3OriginalNormalCoverGeometry Data hF
      (fun p x => Data.phase ν (p,x)) (vref ν) (A ν)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν) cF cT mu) :
    ∀ ν z, z ∈ domain ν ∩ incrementsOriginalParameterRegion Data →
      ∃ i : Fin Data.atlas.count × Fin Data.parameterCount,
        z.1 ∈ (Data.parameterChart i.2).source ∧ z.2 ∈ (Data.atlas.chart i.1).source ∧
        ∃ a : A ν, parameterRound2_originalForwardCoordinates Data i z ∈ (cover ν).original i a := by
  intro ν z hz
  obtain ⟨i,hp,hx,hy⟩ := round3_repair_original_forward_sample Data hd z (by rw [hK]; exact mem_univ _)
  have he := parameterRound2_originalForward_left_inv Data i z hp hx
  have hEval : parameterRound2_originalForwardCoordinates Data i z ∈
      incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν i := by
    refine ⟨hy,?_⟩
    change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterRound2_originalForwardCoordinates Data i z) ∈ domain ν
    rw [he]
    exact hz.1
  obtain ⟨a,ha⟩ := (cover ν).covers i _ hEval
  exact ⟨i,hp,hx,a,ha⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_exists_uniform_actual_normal_rebound_stage

#print axioms GlobalEmbedding.Continuation.round3_repair_normal_physical_cover_of_closed_parameters
