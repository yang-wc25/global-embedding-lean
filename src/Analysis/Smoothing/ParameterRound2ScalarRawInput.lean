import Smoothing.ParameterRound2MeanRawProfiles
import Probes.ActualIncrementRealCoefficientJets

/-! A literal scalar realization of the actual native linear argument.
This fills the raw L/A representation and smoothness fields without adding
any source/free/correction/mean estimates. L is the fixed identity; A is
exactly the original g.linearArgument applied to the actual input tensor. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def parameterRound2_scalarArgumentIdentity : X → ℝ →L[ℝ] ℝ :=
  fun _ => ContinuousLinearMap.id ℝ ℝ

theorem parameterRound2_scalarArgumentIdentity_profiles (O : Set X) (ell : ℝ) :
    ContDiffOn ℝ ∞ (parameterRound2_scalarArgumentIdentity (X := X)) O ∧
    ∀ (k : ℕ) (z : X), ell^k * ‖iteratedFDeriv ℝ k
      (parameterRound2_scalarArgumentIdentity (X := X)) z‖ ≤ 1 := by
  refine ⟨contDiffOn_const,?_⟩
  intro k z
  exact (actual_increment_slow_const_jet_bound (ContinuousLinearMap.id ℝ ℝ) k ell z).trans
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Literal input scalar in the SAME actual adapted chart. -/
def parameterRound2_scalarPrimaryArgument
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (nu : Λ) (beta : Β) (z : Ep × D) : ℝ :=
  g.linearArgument nu z.1 (g.inverse nu beta z.1 z.2)
    (input z.1 (g.inverse nu beta z.1 z.2))

theorem parameterRound2_scalarPrimaryArgument_rep
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (nu : Λ) (beta : Β) (z : Ep × D) :
    parameterRound2_scalarArgumentIdentity z (parameterRound2_scalarPrimaryArgument F g input nu beta z) =
      g.linearArgument nu z.1 (g.inverse nu beta z.1 z.2)
        (input z.1 (g.inverse nu beta z.1 z.2)) := rfl

/-- Native joint argument smoothness on the genuine positive neighborhood
implies scalar A smoothness on the SAME restricted actual chart target. -/
theorem parameterRound2_scalarPrimaryArgument_contDiffOn
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (nu : Λ) (beta : Β)
    (hSource : (g.chart nu beta).source ⊆ W ∩ primary nu)
    (hInv : ContMDiffOn 𝓘(ℝ,Ep × D) ((𝓘(ℝ,Ep)).prod I) ∞
      (g.chart nu beta).symm (g.chart nu beta).target)
    (hInverse : ∀ z ∈ (g.chart nu beta).target,
      (g.chart nu beta).symm z = (z.1,g.inverse nu beta z.1 z.2))
    (hArgument : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : Ep × M => g.linearArgument nu z.1 z.2 (input z.1 z.2)) (W ∩ primary nu)) :
    ContDiffOn ℝ ∞ (parameterRound2_scalarPrimaryArgument F g input nu beta) (g.chart nu beta).target := by
  have hc : ContDiffOn ℝ ∞
      (fun z => g.linearArgument nu ((g.chart nu beta).symm z).1 ((g.chart nu beta).symm z).2
        (input ((g.chart nu beta).symm z).1 ((g.chart nu beta).symm z).2))
      (g.chart nu beta).target :=
    (hArgument.comp hInv (fun z hz => hSource ((g.chart nu beta).symm.map_source hz))).contDiffOn
  apply hc.congr
  intro z hz
  rw [hInverse z hz]
  rfl

#print axioms parameterRound2_scalarArgumentIdentity_profiles
#print axioms parameterRound2_scalarPrimaryArgument_contDiffOn
end GlobalEmbedding.Continuation
