import Smoothing.ParameterRound2OriginalFixedPacket
import Probes.ActualIncrementOriginalCoreFields

/-! Reference normal jets use the fixed given-data packet alone. Neither
the current smoothed map nor its tensor enters this uniform profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem round3_original_fixed_normal_le
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        parameterRound2_originalFixedPacketProfile Data j ell := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans
    ((le_iSup (fun v : Fin Data.primaryCount =>
      max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff v))
        (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
        (max (paperAtlasWeighted 0 j ell
          (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal v))
            (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
          (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data v)
            (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v)))) nu).trans
      (le_max_left _ _))

theorem round3_original_primary_fixed_field_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ}
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (cy : (Fin q → ℝ) ≃L[ℝ] Y)
    (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (actualOriginalPrimaryCoordinateOpen Data nu i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hentry : paperAtlasWeighted 0 j ell f (incrementsOriginalPrimaryDifferentiation Data nu)
      (incrementsOriginalPrimaryEvaluation Data nu) ≤ parameterRound2_originalFixedPacketProfile Data j ell)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (cy ∘ f i ∘ parameterTensorModelEquiv n d) (actualOriginalPrimaryNativeOpen Data nu i) ∧
      ∀ k ≤ j, ∀ z, parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k (cy ∘ f i ∘ parameterTensorModelEquiv n d) z‖ ≤
          (‖cy.toContinuousLinearMap‖*linearModelFactor (parameterTensorModelEquiv n d) j*
            coordinateDimensionFactor (n+d) j)*budget := by
  let O := incrementsOriginalPrimaryDifferentiation Data nu
  let U := actualOriginalPrimaryCoordinateOpen Data nu
  let S := incrementsOriginalPrimaryEvaluation Data nu
  have hO : ∀ i, IsOpen (O i) := actual_original_primaryDifferentiation_open Data hd.primary_open nu
  have hU : ∀ i, IsOpen (U i) := actualOriginalPrimaryCoordinateOpen_isOpen Data hd nu
  have hSU : ∀ i, S i ⊆ U i := actualOriginalPrimaryCoordinateOpen_samples Data hd nu
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  have hfin : paperAtlasWeighted 0 j ell f U S ≠ ⊤ := he ▸ ne_top_of_le_ne_top hfinite hentry
  refine ⟨cy.contDiff.comp_contDiffOn ((hf i).comp
    (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hz => hz)),?_⟩
  intro k hk z hz
  have hh := paperAtlasWeighted_native_shifted_joint_jet_le (parameterTensorModelEquiv n d) cy
    0 j ell hell f U S hU hSU hf hfin i hk (le_refl 0) hz
  simp only [Nat.add_zero] at hh
  rw [← he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    ((ENNReal.toReal_mono hfinite hentry).trans hbudget)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
      (coordinateDimensionFactor_nonneg _ _)))
theorem round3_original_fixed_normal_native_jets
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let f := fun z : X => Data.freeNormal nu ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)
    ContDiffOn ℝ ∞ f (actualOriginalPrimaryNativeOpen Data nu i) ∧
      ∀ k ≤ j, ∀ z, parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ actualOriginalNormalJetCost n d N j*budget := by
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).symm
  have hf : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu) i)
      (actualOriginalPrimaryCoordinateOpen Data nu i) := by
    intro i
    exact actual_original_primary_field_coordinate_smooth Data hd nu (Data.freeNormal nu)
      (hs.normal_joint nu) cy.symm.toContinuousLinearMap i
  have hh := round3_original_primary_fixed_field_jets Data hd nu cy
    (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu)) hf j ell hell
    (round3_original_fixed_normal_le Data nu j ell) hfinite budget hbudget i
  have he : cy ∘ incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (Data.freeNormal nu) i ∘ parameterTensorModelEquiv n d = fun z : X => Data.freeNormal nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
    funext z
    simp only [Function.comp_apply,incrementsOriginalMapCoordinates,
      ContinuousLinearEquiv.symm_apply_apply,actual_original_jointPoint_native,cy]
  rw [he] at hh
  exact hh

#print axioms round3_original_fixed_normal_native_jets
end GlobalEmbedding.Continuation
