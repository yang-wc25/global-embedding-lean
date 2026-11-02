import AuxNormBridge.AllOrderCore
import Smoothing.ParameterProductAtlas
import Smoothing.TensorProductJets

/-!
# Original full joint transition budgets and all-order map profiles

The separate original parameter and spatial product budgets give the
actual joint transition budget with their maximum.  Their exact product
norms are retained, including zero-dimensional parameters.  The compact
core argument then bounds the same original joint coordinate map on the
unchanged source and parameter norm domains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Set Function Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.AuxNormBridge

section ProductDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Projecting the two original partial product maps recovers the genuine
joint map with no norm-comparison loss. -/
theorem joint_jet_le_partial_product_max
    (f : E → E) (g : F → F) (z : E × F)
    (hf : ContDiffAt ℝ ∞ f z.1) (hg : ContDiffAt ℝ ∞ g z.2)
    (k : ℕ) (A B : ℝ)
    (hA : ‖iteratedFDeriv ℝ k (fun x : E × F => (f x.1,x.2)) z‖ ≤ A)
    (hB : ‖iteratedFDeriv ℝ k (fun x : E × F => (x.1,g x.2)) z‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x : E × F => (f x.1,g x.2)) z‖ ≤ max A B := by
  have hfr : ContDiffAt ℝ ∞ (fun x : E × F => f x.1) z := hf.comp z contDiffAt_fst
  have hgr : ContDiffAt ℝ ∞ (fun x : E × F => g x.2) z := hg.comp z contDiffAt_snd
  have hP := hfr.prodMk (contDiffAt_snd : ContDiffAt ℝ ∞ (Prod.snd : E × F → F) z)
  have hS := (contDiffAt_fst : ContDiffAt ℝ ∞ (Prod.fst : E × F → E) z).prodMk hgr
  have hF := (ContinuousLinearMap.fst ℝ E F).norm_iteratedFDeriv_comp_left hP (n := k) (by simp)
  have hG := (ContinuousLinearMap.snd ℝ E F).norm_iteratedFDeriv_comp_left hS (n := k) (by simp)
  rw [iteratedFDeriv_prodMk hfr hgr (i := k) (by simp), ContinuousMultilinearMap.opNorm_prod]
  apply max_le_max
  · exact hF.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le ℝ E F)
      (norm_nonneg _)).trans (by simpa using hA))
  · exact hG.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ E F)
      (norm_nonneg _)).trans (by simpa using hB))
end ProductDerivative

variable {Es Ep M P : Type*}
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [ProperSpace Es]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [ProperSpace Ep]
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ,Es) ∞ M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ,Ep) ∞ P]

private local instance jointChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance jointManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- The original separate joint estimates are sufficient for the product
atlas.  No full-product transition supplier is added to the inputs. -/
theorem original_product_transition_jets
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set Es) (Q : Fin B.count → Set Ep)
    (TP TS : ℕ → ℝ)
    (hParam : ∀ (i j : Fin B.count) (k : ℕ), 1 ≤ k →
      ∀ z : Ep × Es, z.1 ∈ Q i →
      z ∈ (((B.chart i).symm.trans (B.chart j)).prod (OpenPartialHomeomorph.refl Es)).source →
      ‖iteratedFDeriv ℝ k (((B.chart i).symm.trans (B.chart j)).prod
        (OpenPartialHomeomorph.refl Es)) z‖ ≤ TP k)
    (hSpatial : ∀ (i j : Fin A.count) (k : ℕ), 1 ≤ k →
      ∀ z : Ep × Es, z.2 ∈ Omega i →
      z ∈ ((OpenPartialHomeomorph.refl Ep).prod ((A.chart i).symm.trans (A.chart j))).source →
      ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod
        ((A.chart i).symm.trans (A.chart j))) z‖ ≤ TS k) :
    ∀ (i j : Fin (parameterProductAtlas A B).count) (k : ℕ), 1 ≤ k →
      ∀ z ∈ Q (parameterProductIndex A B i).1 ×ˢ Omega (parameterProductIndex A B i).2,
      z ∈ (((parameterProductAtlas A B).chart i).symm.trans
        ((parameterProductAtlas A B).chart j)).source →
      ‖iteratedFDeriv ℝ k (((parameterProductAtlas A B).chart i).symm.trans
        ((parameterProductAtlas A B).chart j)) z‖ ≤ max (TP k) (TS k) := by
  intro i j k hk z hz he
  let p := (B.chart (parameterProductIndex A B i).1).symm.trans
    (B.chart (parameterProductIndex A B j).1)
  let s := (A.chart (parameterProductIndex A B i).2).symm.trans
    (A.chart (parameterProductIndex A B j).2)
  have hp : z.1 ∈ p.source := ⟨he.1.1,he.2.1⟩
  have hs : z.2 ∈ s.source := ⟨he.1.2,he.2.2⟩
  have hps : ContDiffOn ℝ ∞ p p.source :=
    (round3Parameter_partial_trans_smooth _ _
      (contMDiffOn_symm_of_mem_maximalAtlas (hB.chart_mem _))
      (contMDiffOn_of_mem_maximalAtlas (hB.chart_mem _))).contDiffOn
  have hss : ContDiffOn ℝ ∞ s s.source :=
    (round3Parameter_partial_trans_smooth _ _
      (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem _))
      (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem _))).contDiffOn
  exact joint_jet_le_partial_product_max p s z
    (hps.contDiffAt (p.open_source.mem_nhds hp))
    (hss.contDiffAt (s.open_source.mem_nhds hs)) k (TP k) (TS k)
    (hParam _ _ k hk z hz.1 ⟨hp,mem_univ _⟩)
    (hSpatial _ _ k hk z hz.2 ⟨mem_univ _,hs⟩)

/-- Every smooth original map has an all-order profile on the original
joint norm domains, without making either original norm domain compact. -/
theorem original_joint_coordinate_jet_profile_exists
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set Es) (Q : Fin B.count → Set Ep)
    (hTargetS : ∀ i, Omega i ⊆ (A.chart i).target)
    (hTargetP : ∀ i, Q i ⊆ (B.chart i).target)
    (hSamplingS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hSamplingP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (radius : ℝ)
    (hRadiusS : ∀ i y, y ∈ Omega i → ‖y‖ ≤ radius)
    (hRadiusP : ∀ i y, y ∈ Q i → ‖y‖ ≤ radius)
    (TP TS : ℕ → ℝ) (hTP : ∀ k, 0 ≤ TP k) (hTS : ∀ k, 0 ≤ TS k)
    (hParam : ∀ (i j : Fin B.count) (k : ℕ), 1 ≤ k →
      ∀ z : Ep × Es, z.1 ∈ Q i →
      z ∈ (((B.chart i).symm.trans (B.chart j)).prod (OpenPartialHomeomorph.refl Es)).source →
      ‖iteratedFDeriv ℝ k (((B.chart i).symm.trans (B.chart j)).prod
        (OpenPartialHomeomorph.refl Es)) z‖ ≤ TP k)
    (hSpatial : ∀ (i j : Fin A.count) (k : ℕ), 1 ≤ k →
      ∀ z : Ep × Es, z.2 ∈ Omega i →
      z ∈ ((OpenPartialHomeomorph.refl Ep).prod ((A.chart i).symm.trans (A.chart j))).source →
      ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod
        ((A.chart i).symm.trans (A.chart j))) z‖ ≤ TS k)
    (f : P × M → F) (hf : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,F) ∞ f) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ i j k z, z ∈ Q j ×ˢ Omega i →
        ‖iteratedFDeriv ℝ k (f ∘ ((B.chart j).prod (A.chart i)).symm) z‖ ≤ C k := by
  let AB := parameterProductAtlas A B
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hCoreBound : ∀ i, (AB.chart i) '' AB.inner i ⊆ closedBall (0 : Ep × Es) radius := by
    intro i z hz
    obtain ⟨x,hx,rfl⟩ := hz
    have hp := hRadiusP _ _ (hSamplingP _ (bufferedInner_subset_sampling B _
      (bufferedInnerCoordinates_mem B _ hx.1)))
    have hs := hRadiusS _ _ (hSamplingS _ (bufferedInner_subset_sampling A _
      (bufferedInnerCoordinates_mem A _ hx.2)))
    rw [mem_closedBall,dist_zero_right]
    change max ‖B.chart (parameterProductIndex A B i).1 x.1‖
      ‖A.chart (parameterProductIndex A B i).2 x.2‖ ≤ radius
    exact max_le hp hs
  have hLocal : ∀ i, ContDiffOn ℝ ∞ (f ∘ (AB.chart i).symm) (AB.chart i).target := by
    intro i
    letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
    exact (hf.comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (hAB.chart_mem i))).contDiffOn
  obtain ⟨C,hC,hJets⟩ := original_coordinate_jet_profile_exists AB hAB (fun _ => 0) radius
    hCoreBound (fun i => Q (parameterProductIndex A B i).1 ×ˢ Omega (parameterProductIndex A B i).2)
    (fun _ _ hz => ⟨hTargetP _ hz.1,hTargetS _ hz.2⟩)
    (fun k => max (TP k) (TS k)) (fun k => (hTP k).trans (le_max_left _ _))
    (original_product_transition_jets A B hA hB Omega Q TP TS hParam hSpatial) f hLocal
  refine ⟨C,hC,?_⟩
  intro i j k z hz
  have hz' : z ∈ Q (parameterProductIndex A B (finProdFinEquiv (j,i))).1 ×ˢ
      Omega (parameterProductIndex A B (finProdFinEquiv (j,i))).2 := by
    simpa only [parameterProductIndex,Equiv.symm_apply_apply] using hz
  simpa only [AB,parameterProductAtlas,parameterProductIndex,Equiv.symm_apply_apply] using
    hJets (finProdFinEquiv (j,i)) k z hz'

end GlobalEmbedding.Continuation.AuxNormBridge

#print axioms GlobalEmbedding.Continuation.AuxNormBridge.joint_jet_le_partial_product_max
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_product_transition_jets
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_joint_coordinate_jet_profile_exists
