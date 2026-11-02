import NormalPolar.ActualRepairModelFirstDefectMapShift
import Probes.ActualIncrementOriginalCoordinateJets
import Probes.Round3ParameterOriginalTensorNorm

/-! The same joint displacement in every actual parameter chart gives the
original weighted base-two order-j and full joint C2 bounds. Actual derivatives
through j+2 are retained, as are the original differentiation and sample domains.
The only fixed factors come from the source-first and target linear charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualRepairModelFirstDefectObservedMap (A : BufferedAtlas M D)
    (B : Fin c → OpenPartialHomeomorph P Ep) (U : P × M → V)
    (i : Fin A.count × Fin c) : X → V :=
  fun z => U ((B i.2).symm z.1,(A.chart i.1).symm z.2)

def actualRepairModelFirstDefectMapNormCost (m d N j : ℕ) (K : ℝ) : ℝ :=
  (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm (j+2)*
    ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖*K

theorem actualRepairModelFirstDefectMapNormCost_nonneg (m d N j : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ actualRepairModelFirstDefectMapNormCost m d N j K := by
  unfold actualRepairModelFirstDefectMapNormCost
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (linearModelFactor_nonneg _ _)) (norm_nonneg _)) hK

theorem actualRepairModelFirstDefect_map_norms_from_native
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (O : Fin A.count × Fin c → Set X) (hO : ∀ i, IsOpen (O i))
    (hOsub : ∀ i, O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target)
    (hSO : ∀ i, (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ O i)
    (U : P × M → V) (j : ℕ) (tau delta K : ℝ)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hU : ∀ i, ContDiffOn ℝ ∞ (actualRepairModelFirstDefectObservedMap A B U i) (O i))
    (hjet : ∀ i, ∀ k ≤ j+2, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i) z‖ ≤ K*delta*tau) :
    let coordinates := incrementsOriginalMapCoordinates A B U
    let C := actualRepairModelFirstDefectMapNormCost m d N j K
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) := by
  intro coordinates C
  let a := parameterTensorModelEquiv (m+1) d
  let target := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let K0 := linearModelFactor a.symm (j+2)*‖target‖*K
  have hK0 : 0 ≤ K0 := mul_nonneg (mul_nonneg (linearModelFactor_nonneg _ _) (norm_nonneg _)) hK
  let OC := modelCoordinateDomains a O
  have hOC : ∀ i, IsOpen (OC i) := modelCoordinateDomains_open a hO
  have hSOC : ∀ i, S i ⊆ OC i := by
    intro i y hy
    apply hSO i
    change a (a.symm y) ∈ S i
    simpa using hy
  have hOCorig : ∀ i, OC i ⊆ incrementsOriginalDifferentiation A B i := by
    intro i y hy
    have h := hOsub i hy
    exact ⟨h.2,h.1⟩
  have hcoord (i) : coordinates i = target ∘ actualRepairModelFirstDefectObservedMap A B U i ∘ a.symm := rfl
  have hcoords (i) : ContDiffOn ℝ ∞ (coordinates i) (OC i) := by
    rw [hcoord]
    exact target.contDiff.comp_contDiffOn ((hU i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz))
  have hcb : ∀ i, ∀ k ≤ j+2, ∀ y ∈ S i,
      tau^k*‖iteratedFDeriv ℝ k (coordinates i) y‖ ≤ K0*delta*tau := by
    intro i k hk y hy
    have hy' : a (a.symm y) ∈ S i := by simpa using hy
    have hpre := norm_iteratedFDeriv_comp_equiv_le a.symm (actualRepairModelFirstDefectObservedMap A B U i) k y
    have hbpre : tau^k*‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i ∘ a.symm) y‖ ≤
        linearModelFactor a.symm (j+2)*(K*delta*tau) := by
      calc
        _ ≤ tau^k*(‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i) (a.symm y)‖*linearModelFactor a.symm k) :=
          mul_le_mul_of_nonneg_left hpre (pow_nonneg htau.le k)
        _ = linearModelFactor a.symm k*(tau^k*‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i) (a.symm y)‖) := by ring
        _ ≤ _ := mul_le_mul (linearModelFactor_mono a.symm hk) (hjet i k hk _ hy')
          (by positivity) (linearModelFactor_nonneg _ _)
    have hpost := slow_linear_jet_bound target (OC i) (hOC i) (actualRepairModelFirstDefectObservedMap A B U i ∘ a.symm)
      ((hU i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz)) k tau
      (linearModelFactor a.symm (j+2)*(K*delta*tau)) htau.le y (hSOC i hy) hbpre
    rw [hcoord]
    exact hpost.trans_eq (by dsimp only [K0]; ring)
  have hn2 := actualRepairModelFirstDefect_map_base_from_weighted_jets 2 j tau
    (K0*delta*tau) htau htau1 (by positivity) coordinates OC S hOC hSOC hcoords hcb
  have hrestrict := actual_paperAtlasWeighted_open_restrict 2 j tau coordinates
    (incrementsOriginalDifferentiation A B) OC S (parameterRound2_originalDifferentiation_open A B)
    hOC hOCorig hSOC
  rw [← hrestrict] at hn2
  have hbound : (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤
      C*delta/tau := by
    apply hn2.2.trans_eq
    dsimp only [C,actualRepairModelFirstDefectMapNormCost,K0,a,target]
    field_simp <;> ring
  have hc2 := parameterPaperAtlasCj_base_le_weighted 2 j tau coordinates
    (incrementsOriginalDifferentiation A B) S
  exact ⟨fun i => ⟨OC i,hOC i,hSOC i,hOCorig i,hcoords i⟩,
    ⟨hn2.1,hbound⟩,⟨ne_top_of_le_ne_top hn2.1 hc2,(ENNReal.toReal_mono hn2.1 hc2).trans hbound⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_map_norms_from_native
