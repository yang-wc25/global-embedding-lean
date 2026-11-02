import GlobalEmbedding.Offline.BufferedSamplingDomains
import Smoothing.TensorParameterCoordinates

/-!
# Original buffered source and parameter domains for the actual local factory

Both ambient sets are the exact original sampling unions.  The carrier is
formed from the original inner coordinate sets; it may be disconnected or
nonconvex.  The original atlas buffer directly supplies every local ball.
The product coordinates and evaluation domains are the original ones.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Es Ep M P : Type*}
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [TopologicalSpace P]

/-- No chart restriction or new norm domain is made. -/
def sourceCollarNovOriginalOuter (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) : Set (Ep × Es) :=
  bufferedSamplingCoordinates B i.2 ×ˢ bufferedSamplingCoordinates A i.1

def sourceCollarNovOriginalInner (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) : Set (Ep × Es) :=
  bufferedInnerCoordinates B i.2 ×ˢ bufferedInnerCoordinates A i.1

theorem sourceCollarNov_original_outer_open (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) : IsOpen (sourceCollarNovOriginalOuter A B i) :=
  (bufferedSamplingCoordinates_open B i.2).prod (bufferedSamplingCoordinates_open A i.1)

theorem sourceCollarNov_original_buffer (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin A.count × Fin B.count) (r : ℝ) (hS : r ≤ A.buffer) (hP : r ≤ B.buffer)
    (z : Ep × Es) (hz : z ∈ sourceCollarNovOriginalInner A B i) :
    ball z r ⊆ sourceCollarNovOriginalOuter A B i := by
  intro y hy
  have hy' : y ∈ ball z.1 r ×ˢ ball z.2 r := by simpa only [ball_prod_same] using hy
  exact ⟨mem_iUnion.mpr ⟨z.1,mem_iUnion.mpr ⟨hz.1,ball_subset_ball hP hy'.1⟩⟩,
    mem_iUnion.mpr ⟨z.2,mem_iUnion.mpr ⟨hz.2,ball_subset_ball hS hy'.2⟩⟩⟩

theorem sourceCollarNov_original_inner_bounded
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin B.count → Set Ep)
    (hS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (R : ℝ) (hRS : ∀ i x, x ∈ Omega i → ‖x‖ ≤ R)
    (hRP : ∀ i p, p ∈ Q i → ‖p‖ ≤ R) (i : Fin A.count × Fin B.count) :
    sourceCollarNovOriginalInner A B i ⊆ closedBall 0 R := by
  intro z hz
  have hS' := hRS i.1 z.2 (hS i.1 (bufferedInner_subset_sampling A i.1 hz.2))
  have hP' := hRP i.2 z.1 (hP i.2 (bufferedInner_subset_sampling B i.2 hz.1))
  simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff] using And.intro hP' hS'

/-- The original product cutoff is carried by the original inner sets,
without placing an entire original support inside one convex set. -/
theorem sourceCollarNov_original_product_support
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (thetaS : Fin A.count → M → ℝ) (thetaP : Fin B.count → P → ℝ)
    (hS : ∀ i, tsupport (thetaS i) ⊆ A.inner i)
    (hP : ∀ i, tsupport (thetaP i) ⊆ B.inner i) (i : Fin A.count × Fin B.count) :
    tsupport (fun z : P × M => thetaP i.2 z.1 * thetaS i.1 z.2) ⊆
      ((B.chart i.2).prod (A.chart i.1)).source ∩
        ((B.chart i.2).prod (A.chart i.1)) ⁻¹' sourceCollarNovOriginalInner A B i := by
  intro z hz
  have hp := hP i.2 (tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hz))
  have hs := hS i.1 (tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz))
  exact ⟨⟨B.inner_subset i.2 hp,A.inner_subset i.1 hs⟩,
    bufferedInnerCoordinates_mem B i.2 hp,bufferedInnerCoordinates_mem A i.1 hs⟩

section NativeCoordinates
variable {n d : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Epar" => EuclideanSpace ℝ (Fin d)

/-- Every local-buffer point is evaluated in the same original Omega and Q;
the numerical model equivalence is the original one. -/
theorem sourceCollarNov_original_samples
    (A : BufferedAtlas M D) (B : BufferedAtlas P Epar)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Epar)
    (hS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (i : Fin A.count × Fin B.count) (z : Epar × D)
    (hz : z ∈ sourceCollarNovOriginalOuter A B i) :
    parameterTensorModelEquiv n d z ∈ incrementsOriginalEvaluation A B.chart Omega Q univ i := by
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply z)
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) = z.2 at hx
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = z.1 at hp
  refine ⟨?_,?_,?_,mem_univ _⟩
  · change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) ∈ (A.chart i.1).target ∧
      incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) ∈ (B.chart i.2).target
    rw [hx,hp]
    exact ⟨bufferedSampling_subset_target A i.1 hz.2,bufferedSampling_subset_target B i.2 hz.1⟩
  · change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) ∈ Omega i.1
    rw [hx]
    exact hS i.1 hz.2
  · change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) ∈ Q i.2
    rw [hp]
    exact hP i.2 hz.1
end NativeCoordinates

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_buffer
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_product_support
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_samples
