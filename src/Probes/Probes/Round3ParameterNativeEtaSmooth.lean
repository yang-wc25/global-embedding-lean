import Probes.Round3ParameterNativeChartSmooth

/-! The actual subordinate eta in a canonical native target chart is
smooth. Its parameter map is the genuine inverse observer chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_native_eta_target_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (hPreserves : Round3ParameterChartPreserves a)
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a a.source)
    (hai : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target)
    (eta : P × M → ℝ) (hEta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ eta) :
    let aN := round3ParameterChartPullback B a
    ContDiffOn ℝ ∞ (fun z : X => eta (B.symm (aN.symm z).1,(aN.symm z).2)) aN.target := by
  intro aN
  let qM := round3ParameterProductChart (M := M) B
  have haiN := (round3ParameterChartPullback_smooth B hB a ha hai).2
  have hNpreserves : Round3ParameterChartPreserves aN := round3ParameterChartPullback_preserves B a hPreserves
  have hMap : MapsTo aN.symm aN.target qM.target := by
    intro z hz
    have hp : (aN.symm z).1 = z.1 := round3ParameterChartPreserves_inverse aN hNpreserves z hz
    exact ⟨by rw [hp]; exact ((round3ParameterChartPullback_target B a z).mp hz).1,mem_univ _⟩
  have hq := round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B hB
  exact (hEta.comp_contMDiffOn (hq.comp haiN hMap)).contDiffOn

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_eta_target_smooth
