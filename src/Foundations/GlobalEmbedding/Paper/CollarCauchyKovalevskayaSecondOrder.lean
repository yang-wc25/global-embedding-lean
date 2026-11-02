import GlobalEmbedding.Paper.CollarCauchyKovalevskayaJetReduction
import GlobalEmbedding.Paper.CollarCKFiniteDimensionalCodomain

/-!
# The full original analytic second-order Cauchy problem

Source: `literature/parallelizable-stable-plus-one/main.tex`, Theorem `thm:ck`, lines 500–505;
Gantumur, Theorem 18 and Corollary 20. Use the exact original forcing, jet and solution types.
The finite-dimensional first-order output adapter is the sole W5 provider.
-/

open scoped Topology
namespace GlobalEmbedding.Paper

/-- Transfer a genuine prolonged solution and its actual competitor uniqueness to the original
second-order problem. Source: Gantumur, Corollary 20. Accepted actual jet compatibility gives
the original solution. Every original competitor has an actual prolongation solving the same
first-order system; first-order equality then gives equality of the first components. This
intermediate interface is instantiated by the actual solver in the original-parameter theorem. -/
theorem ckSecondOrder_from_prolonged_unique {n m : ℕ}
    (F : CKForcingInput n m → CKVal m) (u₀ u₁ : CKX n → CKVal m)
    (x₀ : CKX n) (ε : ℝ) (hε : 0 < ε) (V : CKJoint n → CKState n m)
    (hV : CKProlongedSolution F u₀ u₁ x₀ ε V)
    (hunique : ∀ W η, 0 < η → CKProlongedSolution F u₀ u₁ x₀ η W →
      ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
        ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), x₀) δ → V (r, x) = W (r, x)) :
    CKOriginalSolution F u₀ u₁ x₀ ε (fun z ↦ (V z).1) ∧
      (∀ v η, 0 < η → CKOriginalSolution F u₀ u₁ x₀ η v →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
          ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), x₀) δ → (V (r, x)).1 = v (r, x)) := by
  refine ⟨ckProlongedSolution_original F u₀ u₁ x₀ ε hε V hV, ?_⟩
  intro v η hη hv
  obtain ⟨δ, hδ, hδε, hδη, heq⟩ := hunique (ckProlongation v) η hη
    (ckOriginalSolution_prolongs F u₀ u₁ x₀ η v hv)
  refine ⟨δ, hδ, hδε, hδη, ?_⟩
  intro r x hx
  exact congrArg Prod.fst (heq r x hx)

/-- The full original finite analytic second-order Cauchy problem has a local jointly analytic
solution, unique against every genuine local analytic competitor.

Source: the paper's Theorem `thm:ck`, Gantumur Theorem 18 and Corollary 20.
Proof: retain exactly the original product state `V=(u,u_x,u_r)`. The accepted jet reduction
makes its actual initial data analytic and makes its first-order RHS analytic at the actual
initial prolonged jet. Apply the sole finite-dimensional real-output first-order CK theorem
once to this same state and data. This gives one positive ball, an actual analytic prolonged
solution, its actual PDE and initial trace, and uniqueness against every actual analytic
prolonged competitor. Accepted compatibility, proved using actual mixed derivatives and normal
constancy, identifies the first component as a genuine original second-order solution on that
same ball. For any original analytic competitor on any positive ball, its actual prolongation
solves the same first-order problem and has the same initial state. The same first-order
uniqueness gives equality on a positive ball bounded by both radii; projecting first components
gives the asserted original uniqueness. All spatial coordinates remain present. Zero spatial
or output dimension is included by the general first-order adapter. No compatibility, formal
identity, convergence bound, or desired solution is an additional original hypothesis. -/
theorem collarCauchyKovalevskayaSecondOrder {n m : ℕ}
    (F : CKForcingInput n m → CKVal m)
    (u₀ u₁ : CKX n → CKVal m) (x₀ : CKX n)
    (hF : AnalyticAt ℝ F (ckForcingInitialPoint u₀ u₁ x₀))
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu₁ : AnalyticAt ℝ u₁ x₀) :
    ∃ ε > 0, ∃ u : CKJoint n → CKVal m,
      CKOriginalSolution F u₀ u₁ x₀ ε u ∧
      (∀ v η, 0 < η → CKOriginalSolution F u₀ u₁ x₀ η v →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
          ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), x₀) δ → u (r, x) = v (r, x)) := by
  obtain ⟨ε, hε, V, ha, hpde, hinit, huniq⟩ :=
    collarCKFiniteDimensionalExistenceUnique (F := CKState n m)
      (ckProlongedRhs F) (ckProlongedInitialData u₀ u₁) x₀
      (ckProlongedInitialData_analyticAt u₀ u₁ x₀ hu₀ hu₁)
      (ckProlongedRhs_analyticAt F u₀ u₁ x₀ hF hu₀ hu₁)
  have hV : CKProlongedSolution F u₀ u₁ x₀ ε V := ⟨ha, hpde, hinit⟩
  refine ⟨ε, hε, (fun z ↦ (V z).1), ?_⟩
  apply ckSecondOrder_from_prolonged_unique F u₀ u₁ x₀ ε hε V hV
  intro W η hη hW
  exact huniq W η hη hW.1 hW.2.1 hW.2.2

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.ckSecondOrder_from_prolonged_unique
#print axioms GlobalEmbedding.Paper.collarCauchyKovalevskayaSecondOrder
