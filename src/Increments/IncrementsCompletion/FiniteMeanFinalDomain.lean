import IncrementsCompletion.OriginalOpenMeanIdentity
import SourceCollarsBridge.FiniteTensorGermSpace
import CollarCompletion.FiniteOpenMeanOperator

/-!
# Finite physical mean residual on the same final construction domain

The finite iteration produces a native tensor E with its original finite
norms and the exact physical identity E = mean(K) - H.  This theorem transfers
that very tensor to the source-slice presentation used by the final finite
increment.  The original parameter region, all original evaluation sets, and
every original weighted norm are retained.  The fast-scale estimate follows
from the same finite seminorm and no compactness hypothesis is needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology Classical
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {Β : Type*} [Fintype Β]

theorem incrementsCompletion_finite_physical_mean_final_domain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hg : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
      ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (ell delta tau : ℝ) (htaul : tau ≤ ell)
    (E : finiteTensorGermSpace Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) (incrementsOriginalParameterRegion Data)
      (fun _ _ hy => hy.1))
    (hE : ∀ z ∈ incrementsOriginalParameterRegion Data, E.val.val z.1 z.2 =
      fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g input hActive length tau z.1 z.2-
        Data.H z.1 z.2)
    (G : Set (P × M)) (hG : IsOpen G)
    (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let F := fullIncrementNovOriginalSourceSlice Data
    let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
    let gG := round3Parameter_restrictPrimaryFamily F
      (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG
    let meanResidual := fun t x => delta^2 •
      (round3ParameterPrimaryMean F hF gG input length tau t x-Data.H t x)
    meanResidual ∈ parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S G ∧
    ∀ j, paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart meanResidual)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart meanResidual)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤
        delta^2 * finiteTensorGermSeminorm Data.atlas Data.parameterChart S
          (incrementsOriginalParameterRegion Data) (fun _ _ hy => hy.1) ell j E := by
  intro S F hF gG meanResidual
  let W := incrementsOriginalParameterRegion Data
  let SE : finiteTensorGermSpace Data.atlas Data.parameterChart S W (fun _ _ hy => hy.1) := delta^2 • E
  have hSG (i) : MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) (S i) G :=
    fun y hy => hKG ⟨hy.2.2.2,mem_univ _⟩
  have heq : ∀ z ∈ G, meanResidual z.1 z.2 = SE.val.val z.1 z.2 := by
    intro z hz
    change delta^2 • (round3ParameterPrimaryMean F hF gG input length tau z.1 z.2-Data.H z.1 z.2) =
      delta^2 • E.val.val z.1 z.2
    rw [round3Parameter_restrictPrimary_mean F hF
      (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG input length tau z hz]
    rw [incrementsCompletion_original_open_primary_mean Data hd hs g hg hTarget hActive
      input length tau z.1 (hGR hz).1 z.2]
    exact congrArg (fun T => delta^2 • T) (hE z (hGR hz)).symm
  have hNorm (j : ℕ) := parameterRound2_originalTensor_weighted_eq_of_sample_germ
    Data.atlas Data.parameterChart S (fun _ _ hy => hy.1) meanResidual SE.val.val G hG hSG heq 0 j tau
  refine ⟨?_,?_⟩
  · constructor
    · exact parameterRound2_tensor_coordinate_germ_transfer Data.atlas Data.parameterChart S
        (fun _ _ hy => hy.1) SE.val.val meanResidual SE.val.property.1 G hG hSG
        (fun z hz => (heq z hz).symm)
    · intro z hz
      rw [heq z hz]
      exact SE.val.property.2 z (hGR hz)
  · intro j
    rw [hNorm j]
    exact CollarCompletion.finite_original_mean_residual_fast_scale Data.atlas Data.parameterChart S W
      (fun _ _ hy => hy.1) ell E j tau delta
      (finiteTensorGermSeminorm Data.atlas Data.parameterChart S W (fun _ _ hy => hy.1) ell j E)
      htaul le_rfl


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_finite_physical_mean_final_domain
