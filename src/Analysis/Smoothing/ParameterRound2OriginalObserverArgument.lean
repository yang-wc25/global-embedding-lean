import Probes.ActualIncrementOriginalCoreFields
import Smoothing.ParameterRound2OriginalArgumentGermProfiles
import Smoothing.ParameterRound2OriginalArgumentGermDifference

/-! The literal original linear argument in the original observation chart.
The input sizes are the unchanged original paper norms, and estimates are
only on the original primary evaluation set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

private theorem parameterRound2_linear_positive_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (ell : ℝ) (k : ℕ) (hk : 1 ≤ k) (z : X) :
    ell^(k-1)*‖iteratedFDeriv ℝ k L z‖ ≤ ‖L‖ := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  cases r with
  | zero =>
    simp only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
    exact le_rfl
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ : X => L := funext (fun y => L.fderiv)
    rw [he,iteratedFDeriv_const_of_ne (by omega : r+1 ≠ 0)]
    simp only [Pi.zero_apply,norm_zero,mul_zero]
    exact L.opNorm_nonneg

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

theorem parameterRound2_original_observer_argument_germ_profiles
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hInput : ∀ a, ∃ UI : Set (Fin (n+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input a) UI)
    (hSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (input p x).IsSymm)
    (j : ℕ) (ell ML MA : ℝ) (hell : 0 < ell)
    (hProfile : incrementsOriginalInputProfileWithLinear Data j ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data j ell).toReal ≤ ML)
    (hInputFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hMA : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ MA)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let a := parameterTensorModelEquiv n d
    let C := actualFastChartTransferPrefix (fun _ => ‖a.toContinuousLinearMap‖) j *
      coordinateDimensionFactor (n+d) j
    let arg := fun z : X => Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
      ((Data.atlas.chart i.1).symm z.2)
      (input ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))
    ∃ V0 : Set X, IsOpen V0 ∧
      a ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i ⊆ V0 ∧
      V0 ⊆ actualOriginalPrimaryNativeOpen Data nu i ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z, a z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤ 2^j*(‖actualOriginalCoefficientFunctional n‖*C*ML)*(C*MA) := by
  intro a C arg
  let T : ℕ → ℝ := fun _ => ‖a.toContinuousLinearMap‖
  have hT : ∀ k, 0 ≤ T k := fun _ => a.toContinuousLinearMap.opNorm_nonneg
  let O := actualOriginalPrimaryNativeOpen Data nu i
  let S := a ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i
  have hSO : S ⊆ O := fun z hz => actualOriginalPrimaryCoordinateOpen_samples Data hd nu i hz
  have hjets : ∀ z ∈ S, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k a z‖ ≤ T k :=
    fun z _ k hk _ => parameterRound2_linear_positive_jet_bound a.toContinuousLinearMap ell k hk z
  obtain ⟨V0,hV0,hSV0,hV0O,hreg,hbound⟩ := parameterRound2_original_argument_germ_profiles
    Data hd hLinear input hInput hSymm j T hT ell hell ML MA hProfile hML hInputFinite hMA
    nu i a O S (actualOriginalPrimaryNativeOpen_isOpen Data hd nu i) hSO
    a.contDiff.contDiffOn (fun _ hz => hz) (fun _ hz => hz) hjets
  have he : (fun z : X => Data.linearArgument nu
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z)).1
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z)).2
      (input (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z)).1
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z)).2)) = arg := by
    funext z
    rw [actual_original_jointPoint_native]
  rw [he] at hreg hbound
  exact ⟨V0,hV0,hSV0,hV0O,hreg,hbound⟩

#print axioms parameterRound2_original_observer_argument_germ_profiles
end GlobalEmbedding.Continuation
