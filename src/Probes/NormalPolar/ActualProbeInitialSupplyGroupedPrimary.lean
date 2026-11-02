import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude
import NormalPolar.JointSecondaryGroupedEvaluation
/-! The physical grouped first array on the original parameter manifold.
The labels remain exactly Λ ⊕ Fin r. Each original prescribed label first
sums its actual subordinate pieces, and the whole parameter field is inserted
before the physical wave or quadratic secondary forcing is formed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {M P Ep Λ Β : Type*}
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β] {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable
    (F : P → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → EuclideanSpace ℝ (Fin (m+1)) → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
      normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
    (u : P → Fin p → ℝ)


variable (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ (l : Λ) (k : Β), Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ (l : Fin r) (s : Pieces l), Round3ParameterChartPreserves (a l s))
include hg ha

theorem actualProbeInitialSupply_grouped_primary_pullback
    (b : Ep) (hb : b ∈ B.target) (x : M) :
    jointGroupedCombinedPrimary
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t))) label
      (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
      (fun l s => round3ParameterChartPullback B (a l s))
      (fun t => input (B.symm t)) (u (B.symm b)) (b,x) =
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta backgroundLength probeLength
      a input u (B.symm b,x) := by
  rw [jointGroupedCombinedPrimary_diagonal
    (fun t => F (B.symm t)) (fun t => hF (B.symm t))
    ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t))) label
    (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t))
    (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
    (fun l s => round3ParameterChartPullback B (a l s))
    (fun t => input (B.symm t)) (fun t => u (B.symm t)) (b,x)]
  unfold actualProbeInitialGroupedPrimary
  apply Finset.sum_congr rfl
  intro l _
  have hr := actualProbeInitialSupply_grouped_amplitude_pullback F hF g label c vf tau delta
    backgroundLength probeLength a input u B hg ha false l b hb x
  have hq := actualProbeInitialSupply_grouped_amplitude_pullback F hF g label c vf tau delta
    backgroundLength probeLength a input u B hg ha true l b hb x
  cases l with
  | inl l =>
    exact congrArg₂ (fun v w : V => Real.cos (g.phase l (B.symm b,x)/tau) • v -
      Real.sin (g.phase l (B.symm b,x)/tau) • w) hr hq
  | inr l =>
    exact congrArg₂ (fun v w : V => Real.cos (phase l (B.symm b,x)/tau) • v -
      Real.sin (phase l (B.symm b,x)/tau) • w) hr hq

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_primary_pullback
