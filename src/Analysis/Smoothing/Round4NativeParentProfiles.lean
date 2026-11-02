import Smoothing.Round4ParentFiniteProfiles
import Probes.Round3PreparedPrimaryPiece

/-! The supported native parameter pullback is exactly the original parent
on each receiving target germ. Its actual all-order joint jets therefore
retain the named raw parent profile and its finite-prefix dependence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es

theorem round4_actual_native_parent_jets
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K : Set P) (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (p i : Fin A.count × Fin c) (j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (y : X) (hy : y ∈ ((parameterLocalProductFamily A B).chart p).target) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i
    ell^j*‖iteratedFDeriv ℝ j
      (round3ParameterNativeParent (B.chart p.2) theta ∘
        (actualOriginalHostJointChart («Ep» := Ep) (A.chart p.1)).symm) y‖ ≤
      round4ParentProfile BS TS BP TP Ds Dp j := by
  classical
  intro theta
  have hPar : y.1 ∈ (B.chart p.2).target := hy.1
  have heq : (round3ParameterNativeParent (B.chart p.2) theta ∘
        (actualOriginalHostJointChart («Ep» := Ep) (A.chart p.1)).symm) =ᶠ[𝓝 y]
      theta ∘ ((parameterLocalProductFamily A B).chart p).symm := by
    filter_upwards [((B.chart p.2).open_target.preimage continuous_fst).mem_nhds hPar] with z hz
    change (if (z.1,(A.chart p.1).symm z.2) ∈ (round3ParameterProductChart (M := M) (B.chart p.2)).target
      then theta ((B.chart p.2).symm z.1,(A.chart p.1).symm z.2) else 0) = _
    rw [ite_eq_left (show (z.1,(A.chart p.1).symm z.2) ∈
      (round3ParameterProductChart (M := M) (B.chart p.2)).target from ⟨hz,mem_univ _⟩)]
    rfl
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact round4_actual_product_parent_jets BS TS BP TP hBS hTS hBP hTP Ds Dp
    A B hA hB K RS RP p i j ell hell hell1 y hy

#print axioms round4_actual_native_parent_jets
end GlobalEmbedding.Continuation
