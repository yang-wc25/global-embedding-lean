import Probes.Round4UniformFreeNormalCoordinate
import Mathlib.Analysis.Calculus.MeanValue

/-!
The dimension-produced ambient coordinate remains nonzero on a quantitative
neighborhood. Its radius reads only first frame jets and fixed coercivity
margins. The unit free-normal field is then the actual normalized double
projection, with no assumed normal field or projection-norm reserve.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Metric
open scoped ContDiff Topology NNReal
namespace GlobalEmbedding.Continuation

def round4FreeProjectionFirstCost (cA cB MA MB : ℝ) : ℝ :=
  2 * actualFreeNormalProjectionCost 1 cB MB * actualFreeNormalProjectionCost 1 cA MA

theorem round4FreeProjectionFirstCost_nonneg {cA cB MA MB : ℝ}
    (hcA : 0 < cA) (hcB : 0 < cB) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB) :
    0 ≤ round4FreeProjectionFirstCost cA cB MA MB := by
  unfold round4FreeProjectionFirstCost
  exact mul_nonneg
    (mul_nonneg (by norm_num) (actualFreeNormalProjectionCost_nonneg 1 hcB hMB))
    (actualFreeNormalProjectionCost_nonneg 1 hcA hMA)

def round4FreeNormalNeighborhoodRadius (N : ℕ) (cA cB MA MB : ℝ) : ℝ :=
  (round4AmbientCoordinateReserve N / 2) / (round4FreeProjectionFirstCost cA cB MA MB + 1)

variable {D E T : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  {N : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin N)
private local instance neighborhoodOperatorNormed : NormedAddCommGroup (V →L[ℝ] V) :=
  inferInstance
private local instance neighborhoodOperatorSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  inferInstance

theorem round4_actual_free_projection_lipschitz
    (cA cB MA MB : ℝ) (hcA : 0 < cA) (hcB : 0 < cB)
    (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (A : D → E →L[ℝ] V) (B : D → T →L[ℝ] V)
    (O : Set D) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hAr : ∀ x ∈ O, ∀ v : E, cA*‖v‖^2 ≤ ‖A x v‖^2)
    (hBr : ∀ x ∈ O, ∀ v : T, cB*‖v‖^2 ≤ ‖B x v‖^2)
    (hAj : ∀ k ≤ 1, ∀ x ∈ O, ‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hBj : ∀ k ≤ 1, ∀ x ∈ O, ‖iteratedFDeriv ℝ k B x‖ ≤ MB)
    (v : V) (hv : ‖v‖ ≤ 1) :
    ContDiffOn ℝ ∞ (fun x => actualFreeNormalProjectionRaw (A x) (B x) v) O ∧
    LipschitzOnWith
      ⟨round4FreeProjectionFirstCost cA cB MA MB,
        round4FreeProjectionFirstCost_nonneg hcA hcB hMA hMB⟩
      (fun x => actualFreeNormalProjectionRaw (A x) (B x) v) O := by
  let PA := actualFreeNormalProjectionCost 1 cA MA
  let PB := actualFreeNormalProjectionCost 1 cB MB
  have hPA : 0 ≤ PA := actualFreeNormalProjectionCost_nonneg 1 hcA hMA
  have hPB : 0 ≤ PB := actualFreeNormalProjectionCost_nonneg 1 hcB hMB
  let QA := fun x => (LinearMap.range (A x).toLinearMap)ᗮ.starProjection
  let QB := fun x => (LinearMap.range (B x).toLinearMap)ᗮ.starProjection
  obtain ⟨hQA, hQAj⟩ := actual_normal_projection_slow_jets_on_samples A O O hO Subset.rfl hA
    (fun x hx => actual_frame_injective_of_reserve (A x) cA hcA (hAr x hx))
    1 1 cA MA (by norm_num) hcA hMA hAr (by simpa only [one_pow, one_mul] using hAj)
  obtain ⟨hQB, hQBj⟩ := actual_normal_projection_slow_jets_on_samples B O O hO Subset.rfl hB
    (fun x hx => actual_frame_injective_of_reserve (B x) cB hcB (hBr x hx))
    1 1 cB MB (by norm_num) hcB hMB hBr (by simpa only [one_pow, one_mul] using hBj)
  let Q : D → V →L[ℝ] V := fun x => (QB x).comp (QA x)
  have hQ : ContDiffOn ℝ ∞ Q O := hQB.clm_comp hQA
  have hQone (x : D) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ 1 Q x‖ ≤ round4FreeProjectionFirstCost cA cB MA MB := by
    have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ V V V)
      (ContinuousLinearMap.norm_compL_le ℝ V V V) O hO QB QA hQB hQA 1 1 PB PA
      (by norm_num) hPB x hx
      (fun k hk => hQBj k hk x hx) (fun k hk => hQAj k hk x hx)
    change 1^1 * ‖iteratedFDeriv ℝ 1 Q x‖ ≤ 2^1 * PB * PA at hb
    change ‖iteratedFDeriv ℝ 1 Q x‖ ≤ 2 * PB * PA
    simpa only [one_pow, one_mul, pow_one] using hb
  let raw := fun x => actualFreeNormalProjectionRaw (A x) (B x) v
  have hRaw : ContDiffOn ℝ ∞ raw O := hQ.clm_apply contDiffOn_const
  refine ⟨hRaw, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x hx => (hRaw.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)) _ hConv
  intro x hx
  change ‖fderiv ℝ raw x‖ ≤ round4FreeProjectionFirstCost cA cB MA MB
  rw [← norm_iteratedFDeriv_one]
  have heval := norm_iteratedFDeriv_clm_apply_const
    (hQ.contDiffAt (hO.mem_nhds hx)) (n := 1) (c := v) (by simp)
  exact heval.trans ((mul_le_mul hv (hQone x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem round4_actual_uniform_free_normal_neighborhood
    (cA cB MA MB : ℝ) (hcA : 0 < cA) (hcB : 0 < cB)
    (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (A : D → E →L[ℝ] V) (B : D → T →L[ℝ] V)
    (O : Set D) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hAr : ∀ x ∈ O, ∀ v : E, cA*‖v‖^2 ≤ ‖A x v‖^2)
    (hBr : ∀ x ∈ O, ∀ v : T, cB*‖v‖^2 ≤ ‖B x v‖^2)
    (hAj : ∀ k ≤ 1, ∀ x ∈ O, ‖iteratedFDeriv ℝ k A x‖ ≤ MA)
    (hBj : ∀ k ≤ 1, ∀ x ∈ O, ‖iteratedFDeriv ℝ k B x‖ ≤ MB)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ T < N)
    (hRange : ∀ x ∈ O, LinearMap.range (B x).toLinearMap ≤ (LinearMap.range (A x).toLinearMap)ᗮ)
    (x : D) (hx : x ∈ O) :
    let rho := round4FreeNormalNeighborhoodRadius N cA cB MA MB
    0 < rho ∧ ∃ i : Fin N,
      let raw := fun y => actualFreeNormalProjectionRaw (A y) (B y) (EuclideanSpace.single i 1)
      ContDiffOn ℝ ∞ (NormedSpace.normalize ∘ raw) (O ∩ ball x rho) ∧
      ∀ y ∈ O ∩ ball x rho,
        round4AmbientCoordinateReserve N / 2 ≤ ‖raw y‖ ∧
        ‖NormedSpace.normalize (raw y)‖ = 1 ∧
        NormedSpace.normalize (raw y) ∈ (LinearMap.range (A y).toLinearMap)ᗮ ∧
        NormedSpace.normalize (raw y) ∈ (LinearMap.range (B y).toLinearMap)ᗮ := by
  let K := round4FreeProjectionFirstCost cA cB MA MB
  have hK : 0 ≤ K := round4FreeProjectionFirstCost_nonneg hcA hcB hMA hMB
  have hmu := round4AmbientCoordinateReserve_pos N
  have hKone : 0 < K+1 := by linarith
  have hrho : 0 < round4FreeNormalNeighborhoodRadius N cA cB MA MB :=
    div_pos (div_pos hmu (by norm_num)) hKone
  refine ⟨hrho, ?_⟩
  obtain ⟨i, hi⟩ := round4_actual_free_normal_coordinate_reserve (A x) (B x) hdim
  let v : V := EuclideanSpace.single i 1
  have hv : ‖v‖ ≤ 1 := by simp [v]
  obtain ⟨hRaw, hLip⟩ := round4_actual_free_projection_lipschitz cA cB MA MB hcA hcB hMA hMB
    A B O hO hConv hA hB hAr hBr hAj hBj v hv
  let raw := fun y => actualFreeNormalProjectionRaw (A y) (B y) v
  have hReserve (y : D) (hy : y ∈ O ∩ ball x (round4FreeNormalNeighborhoodRadius N cA cB MA MB)) :
      round4AmbientCoordinateReserve N / 2 ≤ ‖raw y‖ := by
    have hdist : dist x y * (K+1) < round4AmbientCoordinateReserve N / 2 := by
      apply (lt_div_iff₀ hKone).mp
      simpa only [round4FreeNormalNeighborhoodRadius, dist_comm] using mem_ball.mp hy.2
    have hrawdist := hLip.dist_le_mul x hx y hy.1
    have hdiff : ‖raw x‖ - ‖raw y‖ ≤ dist (raw x) (raw y) := by
      rw [dist_eq_norm]
      exact norm_sub_norm_le _ _
    change dist (raw x) (raw y) ≤ K * dist x y at hrawdist
    change round4AmbientCoordinateReserve N ≤ ‖raw x‖ at hi
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hnonzero (y : D) (hy : y ∈ O ∩ ball x (round4FreeNormalNeighborhoodRadius N cA cB MA MB)) :
      raw y ≠ 0 := norm_pos_iff.mp ((div_pos hmu (by norm_num)).trans_le (hReserve y hy))
  refine ⟨i, ?_, ?_⟩
  · exact actual_normalize_contDiffOn.comp (hRaw.mono inter_subset_left)
      (fun y hy => hnonzero y hy)
  · intro y hy
    have hm := actual_free_normal_projection_mem (A y) (B y) v (hRange y hy.1)
    exact ⟨hReserve y hy, NormedSpace.norm_normalize (hnonzero y hy),
      (LinearMap.range (A y).toLinearMap)ᗮ.smul_mem _ hm.1,
      (LinearMap.range (B y).toLinearMap)ᗮ.smul_mem _ hm.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_free_projection_lipschitz
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_free_normal_neighborhood
