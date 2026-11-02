import Probes.ActualUniformRawAnalyticStatement

/-! The finite-increment estimate with C_j and epsilon0 before the actual
atlas, target and smoothing scale. No desired output norm is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem exists_uniform_actual_raw_analytic_budgets
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Brest Mrest Kcut : ℕ → ℝ)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ CR CU : ℕ → ℝ, (∀ j, 0 ≤ CR j) ∧ (∀ j, 0 ≤ CU j) ∧
      ActualRawAnalyticBudget (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
        (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
        q Rsub Lprimary Rsecondary reserve Brest Mrest Kcut T Tinv Tobs TP CR CU := by
  have hrest (j : ℕ) := actual_original_raw_metric_germ_remainder_uniform
    (m := m) (d := d) (N := N) (pcount := c) (M := M) (Tr := Tr) (Label := Label)
    (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary hq
    (by dsimp only [actualSecondarySolveOrder]; omega)
    (by dsimp only [actualSecondarySolveOrder,actualSecondaryInputOrder]; omega)
    reserve (Brest j) (Mrest j) (Kcut j) hc (hBrest j) (hMrest j) (hKcut j)
    T Tinv Tobs TP hT hTinv hTobs hTP
  let R0 : ℕ → ℝ := fun j => Classical.choose (hrest j)
  have hR0 (j) : 0 ≤ R0 j := (Classical.choose_spec (hrest j)).1
  have hrestBound (j) := (Classical.choose_spec (hrest j)).2
  have hwave (j : ℕ) := actual_original_increment_raw_paper_norms_uniform
    (m := m) (d := d) (N := N) (pcount := c) (M := M) (Tr := Tr) (Label := Label)
    (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary hq
    (by dsimp only [actualSecondarySolveOrder]; omega)
    (by dsimp only [actualSecondarySolveOrder,actualSecondaryInputOrder]; omega)
    reserve (Brest j) (Mrest j) (Kcut j) hc (hBrest j) (hMrest j) (hKcut j)
    T Tinv Tobs TP hT hTinv hTobs hTP
  let CU : ℕ → ℝ := fun j => Classical.choose (hwave j)
  have hCU (j) : 0 ≤ CU j := (Classical.choose_spec (hwave j)).1
  have hwaveBound (j) := (Classical.choose_spec (hwave j)).2
  let CR := fun j => (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*R0 j
  have hCR (j) : 0 ≤ CR j := mul_nonneg
    (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) (hR0 j)
  refine ⟨CR,CU,hCR,hCU,?_⟩
  unfold ActualRawAnalyticBudget
  intro j A B hA hB F hF g input inputbar W primary S hSO ell delta tau Delta htau htaul hell1
    hdelta hdeltatau choice raw Obs obs hParam U coordinates Rest
  have hh := hrestBound j A B hA hB F hF g input inputbar W primary S hSO
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs
    (fun i z hz k hk hkj => hParam i z hz k hk (by omega))
  have hu := hwaveBound j A B hA hB F hF g input inputbar W primary S hSO
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs hParam
  exact ⟨hh.1,hh.2.2,hu⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.exists_uniform_actual_raw_analytic_budgets
