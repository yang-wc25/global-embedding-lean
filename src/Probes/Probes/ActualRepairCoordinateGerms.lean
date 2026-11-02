import Probes.ActualSecondaryTotalMetricCoordinates
import Smoothing.ParameterRound2CrossInputJets

/-! A genuine smooth original coordinate germ gives the actual source slice
manifold derivative at that sample. No global smooth extension of U is used;
the true inverse chart germ carries the derivative back to the manifold. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_source_mdifferentiable_of_inverse_chart
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (f : M → V) (y : D) (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ (f ∘ e.symm) y) :
    MDifferentiableAt 𝓙 𝓘(ℝ,V) f (e.symm y) := by
  have hemd : e.MDifferentiable 𝓙 𝓘(ℝ,D) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have ho : MDifferentiableAt 𝓘(ℝ,D) 𝓘(ℝ,V) (f ∘ e.symm) (e (e.symm y)) := by
    rw [e.right_inv hy]
    exact hf.mdifferentiableAt
  have hcomp := ho.comp (e.symm y) (hemd.mdifferentiableAt (e.map_target hy))
  have heq : f =ᶠ[𝓝 (e.symm y)] ((f ∘ e.symm) ∘ e) := by
    filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
    simp only [Function.comp_apply,e.left_inv hx]
  exact hcomp.congr_of_eventuallyEq heq

theorem actual_source_slice_mdifferentiable_of_original_coordinate_germ
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (U : P × M → V) (i : Fin A.count × Fin c) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i)
    (hU : ContDiffAt ℝ ∞ (incrementsOriginalMapCoordinates A B U i) y) :
    MDifferentiableAt 𝓙 𝓘(ℝ,V)
      (fun x => U ((B i.2).symm (incrementsOriginalParameterPoint y),x))
      ((A.chart i.1).symm (incrementsOriginalSourcePoint y)) := by
  let a := parameterTensorModelEquiv n d
  let z := a.symm y
  let f := fun z : X => U ((B i.2).symm z.1,(A.chart i.1).symm z.2)
  have hn : ContDiffAt ℝ ∞ f z := by
    dsimp only [f]
    rw [parameterRound2_nativeMapChart_eq_coordinate A B U i]
    have hh : ContDiffAt ℝ ∞ (incrementsOriginalMapCoordinates A B U i) (a z) := by
      simpa only [z,a.apply_symm_apply] using hU
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.contDiffAt.comp z
      (hh.comp z a.contDiff.contDiffAt)
  have hs : DifferentiableAt ℝ (fun x => U ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2 :=
    (hn.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact actual_source_mdifferentiable_of_inverse_chart (A.chart i.1) (hA.chart_mem i.1)
    (fun x => U ((B i.2).symm z.1,x)) z.2 hy.1 hs

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_source_slice_mdifferentiable_of_original_coordinate_germ
