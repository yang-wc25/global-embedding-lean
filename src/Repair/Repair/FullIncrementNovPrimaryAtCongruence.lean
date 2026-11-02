import Repair.FullIncrementNovPrimaryAtParameter
import Repair.FullIncrementNovPrimarySliceCongruence

/-! Equality of the actual finite differential formula at two presentations
of the same physical parameter.  The parameter spaces may be different and
only the two source slices need smoothness.  This is the open-parameter
replacement for a global heterogeneous equality of primary-family records. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N : ℕ} {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem fullIncrementNov_primary_evaluation_congr
    (F : P → M → V) (F' : Q → M → V)
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F')
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (input' : (p : Q) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (nu : Label) (beta : Sub) (p : P) (p' : Q)
    (hp : ContMDiff I 𝓘(ℝ,V) ∞ (F p)) (hp' : ContMDiff I 𝓘(ℝ,V) ∞ (F' p'))
    (hF : F p = F' p') (hInput : input p = input' p')
    (hCut : ∀ x, g.cutoff nu (p,x) = g'.cutoff nu (p',x))
    (hNormal : ∀ x, g.normal nu (p,x) = g'.normal nu (p',x))
    (hLinear : ∀ x, g.linearArgument nu p x = g'.linearArgument nu p' x)
    (hEta : ∀ x, g.eta nu beta (p,x) = g'.eta nu beta (p',x))
    (hTarget : ∀ x, (p,x) ∈ (g.chart nu beta).target ↔ (p',x) ∈ (g'.chart nu beta).target)
    (hInverse : g.inverse nu beta p = g'.inverse nu beta p') :
    (∀ x, fullIncrementNovPrimarySourceAt F g input tau nu beta p hp x =
      fullIncrementNovPrimarySourceAt F' g' input' tau nu beta p' hp' x) ∧
    fullIncrementNovPrimaryFiniteUAt F g input length tau nu beta p hp =
      fullIncrementNovPrimaryFiniteUAt F' g' input' length tau nu beta p' hp' ∧
    ∀ channel x, fullIncrementNovPrimaryLocalZAt F g input length tau channel nu beta p hp x =
      fullIncrementNovPrimaryLocalZAt F' g' input' length tau channel nu beta p' hp' x := by
  have hFree (x : D) :
      (round3ParameterPrimaryLocalFree F g input tau nu beta p x : V) =
        (round3ParameterPrimaryLocalFree F' g' input' tau nu beta p' x : V) := by
    have hArg : g.linearArgument nu p (g.inverse nu beta p x) (input p (g.inverse nu beta p x)) =
        g'.linearArgument nu p' (g'.inverse nu beta p' x) (input' p' (g'.inverse nu beta p' x)) := by
      rw [hLinear,hInput]
      exact congrArg (fun y => g'.linearArgument nu p' y (input' p' y)) (congrFun hInverse x)
    unfold round3ParameterPrimaryLocalFree round3ParameterPrimaryB
    by_cases hx : (p,x) ∈ (g.chart nu beta).target
    · simp only [hx,(hTarget x).mp hx,dite_true,Submodule.coe_smul_of_tower]
      simp only [hArg,hInverse,hCut,hNormal,hEta]
    · simp only [hx,not_congr (hTarget x) |>.mp hx,dite_false,Submodule.coe_zero]
  have hSource : fullIncrementNovPrimarySourceAt F g input tau nu beta p hp =
      fullIncrementNovPrimarySourceAt F' g' input' tau nu beta p' hp' := by
    have hh := fullIncrementNov_mode_source_congr (F p) (F' p') hp hp'
      (g.inverse nu beta p) (g'.inverse nu beta p') hF hInverse (fun _ _ _ => 0)
      (round3ParameterPrimaryLocalFree F g input tau nu beta p)
      (round3ParameterPrimaryLocalFree F' g' input' tau nu beta p') hFree
    funext x
    exact congrArg incrementsModeComplexInclude (congrFun hh x)
  have hU : fullIncrementNovPrimaryFiniteUAt F g input length tau nu beta p hp =
      fullIncrementNovPrimaryFiniteUAt F' g' input' length tau nu beta p' hp' := by
    have hAB := fullIncrementNov_mode_firstOrder_congr (F p) (F' p') hp hp'
      (g.inverse nu beta p) (g'.inverse nu beta p') hF hInverse
    simp only [fullIncrementNovPrimaryFiniteUAt,hSource,hAB.1,hAB.2]
  refine ⟨fun x => congrFun hSource x,hU,?_⟩
  intro channel x
  unfold fullIncrementNovPrimaryLocalZAt
  apply congrFun (fullIncrementNov_mode_fullReconstruction_congr (F p) (F' p') hp hp'
    (g.inverse nu beta p) (g'.inverse nu beta p') hF hInverse _ _ ?_ (fun _ _ _ => 0) _ _ ?_) x
  · simp only [hU]
  · intro y
    cases channel <;> simp only [Bool.false_eq_true,ite_false,ite_true,Submodule.coe_zero,hFree]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_evaluation_congr
