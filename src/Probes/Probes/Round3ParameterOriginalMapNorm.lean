import Probes.ActualOriginalIncrementNormShift
import Probes.ActualIncrementOriginalCoordinateJets
import Probes.Round3ParameterOriginalTensorNorm

/-! True joint jets in all original parameter charts give the unchanged
original displacement norms.  The only conversion factor is the fixed
source-first model equivalence and target coordinate map, not the number of
parameter charts.  Domains are the original open differentiation domains and
jets include every source and parameter direction. -/

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

def round3ParameterObservedMap (A : BufferedAtlas M D)
    (B : Fin c → OpenPartialHomeomorph P Ep) (U : P × M → V)
    (i : Fin A.count × Fin c) : X → V :=
  fun z => U ((B i.2).symm z.1,(A.chart i.1).symm z.2)

def round3ParameterMapNormCost (m d N j : ℕ) (K : ℝ) : ℝ :=
  (j+2)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm (j+1)*
    ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖*K

theorem round3ParameterMapNormCost_nonneg (m d N j : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ round3ParameterMapNormCost m d N j K := by
  unfold round3ParameterMapNormCost
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (linearModelFactor_nonneg _ _)) (norm_nonneg _)) hK

theorem round3Parameter_original_map_norms_from_native
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (O : Fin A.count × Fin c → Set X) (hO : ∀ i, IsOpen (O i))
    (hOsub : ∀ i, O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target)
    (hSO : ∀ i, (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ O i)
    (U : P × M → V) (j : ℕ) (tau delta K : ℝ)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hU : ∀ i, ContDiffOn ℝ ∞ (round3ParameterObservedMap A B U i) (O i))
    (hjet : ∀ i, ∀ k ≤ j+1, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (round3ParameterObservedMap A B U i) z‖ ≤ K*delta*tau) :
    let coordinates := incrementsOriginalMapCoordinates A B U
    let C := round3ParameterMapNormCost m d N j K
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta*tau) ∧
    (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta) := by
  intro coordinates C
  let a := parameterTensorModelEquiv (m+1) d
  let target := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let K0 := linearModelFactor a.symm (j+1)*‖target‖*K
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
  have hcoord (i) : coordinates i = target ∘ round3ParameterObservedMap A B U i ∘ a.symm := rfl
  have hcoords (i) : ContDiffOn ℝ ∞ (coordinates i) (OC i) := by
    rw [hcoord]
    exact target.contDiff.comp_contDiffOn ((hU i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz))
  have hcb : ∀ i, ∀ k ≤ j+1, ∀ y ∈ S i,
      tau^k*‖iteratedFDeriv ℝ k (coordinates i) y‖ ≤ K0*delta*tau := by
    intro i k hk y hy
    have hy' : a (a.symm y) ∈ S i := by simpa using hy
    have hpre := norm_iteratedFDeriv_comp_equiv_le a.symm (round3ParameterObservedMap A B U i) k y
    have hbpre : tau^k*‖iteratedFDeriv ℝ k (round3ParameterObservedMap A B U i ∘ a.symm) y‖ ≤
        linearModelFactor a.symm (j+1)*(K*delta*tau) := by
      calc
        _ ≤ tau^k*(‖iteratedFDeriv ℝ k (round3ParameterObservedMap A B U i) (a.symm y)‖*linearModelFactor a.symm k) :=
          mul_le_mul_of_nonneg_left hpre (pow_nonneg htau.le k)
        _ = linearModelFactor a.symm k*(tau^k*‖iteratedFDeriv ℝ k (round3ParameterObservedMap A B U i) (a.symm y)‖) := by ring
        _ ≤ _ := mul_le_mul (linearModelFactor_mono a.symm hk) (hjet i k hk _ hy')
          (by positivity) (linearModelFactor_nonneg _ _)
    have hpost := slow_linear_jet_bound target (OC i) (hOC i) (round3ParameterObservedMap A B U i ∘ a.symm)
      ((hU i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz)) k tau
      (linearModelFactor a.symm (j+1)*(K*delta*tau)) htau.le y (hSOC i hy) hbpre
    rw [hcoord]
    exact hpost.trans_eq (by dsimp only [K0]; ring)
  have hn0 := parameterRound2_paperAtlasWeighted_le_of_weighted_jets (j+1) tau
    (K0*delta*tau) htau htau1 (by positivity) coordinates OC S hOC hSOC hcoords hcb
  have hn1 := actual_paper_base_one_from_weighted_jets j tau
    (K0*delta*tau) htau htau1 (by positivity) coordinates OC S hOC hSOC hcoords hcb
  have hrestrict (base r : ℕ) := actual_paperAtlasWeighted_open_restrict base r tau coordinates
    (incrementsOriginalDifferentiation A B) OC S (parameterRound2_originalDifferentiation_open A B)
    hOC hOCorig hSOC
  rw [← hrestrict 0 (j+1)] at hn0
  rw [← hrestrict 1 j] at hn1
  refine ⟨fun i => ⟨OC i,hOC i,hSOC i,hOCorig i,hcoords i⟩,⟨hn0.1,?_⟩,⟨hn1.1,?_⟩⟩
  · exact hn0.2.trans_eq (by dsimp only [C,round3ParameterMapNormCost,K0]; push_cast; ring)
  · have hcancel : K0*delta*tau/tau = K0*delta := mul_div_cancel_right₀ _ htau.ne'
    rw [hcancel] at hn1
    have hj : (j+1 : ℝ) ≤ j+2 := by linarith
    exact hn1.2.trans ((mul_le_mul_of_nonneg_right hj (mul_nonneg hK0 hdelta)).trans_eq
      (by dsimp only [C,round3ParameterMapNormCost,K0]; ring))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_map_norms_from_native
