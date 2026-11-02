import Repair.IncrementGivenPhaseNorms
import Repair.IncrementGivenPhaseTransitionNorms
import Repair.ReferenceOriginalLocalFactoryPhases

/-! The same actual weighted factory datum supplies every phase and
 original-transition component of Given. The covector/weight cap is fixed
 numerically before the seed; all norms are the unchanged original norms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
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
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

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
  (hseed : RepairReferenceSeedDomains seed)
  (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)


include hF Htensor O K center in
theorem increment_given_actual_factory_phase_norms
    (rho transitionBound : ℝ) (hT : 0 ≤ transitionBound)
    (labelBound : ℕ)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let positive := repairReferencePositiveData raw rho
    let base := repairReferenceSignedHierarchy b.cover b.operatorBound transitionBound
    let weight := fun nu => base ^ label nu
    let cap := base^labelBound
    let data := repairReferenceWeightedData positive weight
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1),
    (∀ nu,
      (paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates data nu)
        (incrementsOriginalPrimaryDifferentiation data nu) (incrementsOriginalPrimaryEvaluation data nu) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates data nu)
          (incrementsOriginalPrimaryDifferentiation data nu) (incrementsOriginalPrimaryEvaluation data nu)).toReal ≤
          (j+1)*bufferedTransitionPrefix (incrementGivenPhaseTotalProfile (m+1) d cap b.cover.covectorBound Spatial) j) ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates data nu)
        (incrementsOriginalPrimaryDifferentiation data nu) (incrementsOriginalPrimaryEvaluation data nu) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates data nu)
          (incrementsOriginalPrimaryDifferentiation data nu) (incrementsOriginalPrimaryEvaluation data nu)).toReal ≤
          (j+1)*bufferedTransitionPrefix (incrementGivenPhaseSpatialProfile (m+1) d cap b.cover.covectorBound Spatial) j)) ∧
    (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates data)
      (actualOriginalGivenTransitionDomain data) (actualOriginalGivenTransitionSample data) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates data)
        (actualOriginalGivenTransitionDomain data) (actualOriginalGivenTransitionSample data)).toReal ≤
        (j+1)*bufferedTransitionPrefix (incrementGivenTransitionProfile (m+1) d Parameter Spatial) j) := by
  intro raw positive base weight cap data hd hs Parameter Spatial hParameter hSpatial transition j ell hell hell1
  let index := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  let owner : Fin data.primaryCount → Fin data.atlas.count := fun nu => (index nu).1.1
  let xi : Fin data.primaryCount → D →L[ℝ] ℝ :=
    fun nu => (b.cover.template ((family (index nu).1).pick (index nu).2.1)).covectors (index nu).2.2
  have hBase : 1 < base := repairReferenceSignedHierarchy_gt_one b.cover b.operatorBound transitionBound hT
  have hCap : 0 ≤ cap := pow_nonneg (zero_lt_one.trans hBase).le _
  have hWeight (nu) : |weight nu| ≤ cap := by
    rw [abs_of_nonneg (pow_nonneg (zero_lt_one.trans hBase).le _)]
    exact pow_le_pow_right₀ hBase.le (hLabel nu)
  have hXi (nu) : ‖xi nu‖ ≤ b.cover.covectorBound :=
    (b.cover.bounds ((family (index nu).1).pick (index nu).2.1)).2.2.2.2 (index nu).2.2
  have hPhase (nu) : data.phase nu = fun z => weight nu*xi nu (data.atlas.chart (owner nu) z.2) := rfl
  have hSource (nu) (z) (hz : z ∈ data.primaryDomain nu) : z.2 ∈ (data.atlas.chart (owner nu)).source :=
    (repair_reference_original_family_operator b seed hF Htensor S O K center family hseed outer nu z hz).1
  exact ⟨fun nu => increment_given_actual_phase_weighted_norms data hd hs owner xi weight cap b.cover.covectorBound
      hCap b.cover.covectorBound_pos.le hWeight hXi hPhase hSource Parameter Spatial hSpatial transition
      nu j ell hell hell1,
    increment_given_actual_transition_weighted_norm data hd Parameter Spatial hParameter hSpatial transition j ell hell hell1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_actual_factory_phase_norms
