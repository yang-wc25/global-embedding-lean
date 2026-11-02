import GlobalEmbedding.Paper.IncrementsMeanQuadraticRemainder
import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder
import GlobalEmbedding.Paper.PaperCoordinateNormBridge
import Mathlib.Analysis.Complex.Basic

/-!
# Literal paper norm of the actual real mean-remainder components

Source: original `lem:increments`, main.tex645–661. Exclusive W1 consumer.
No new norm/carrier is introduced. The real coordinate below is the SAME scalar
coefficient, in the native one-component coordinates accepted by the paper bridge.
Quantitative remainder and cumulative-Cj normal imports are added after publication.
-/

noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Paper

/-- The actual real part of one coefficient in native paper coordinates.
Source: real tensor coefficients in original main.tex645–661. -/
def incrementsMeanRealCoordinate : ℂ →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ ↦ Complex.reCLM

/-- This genuine coordinate projection has norm at most one; no complex/real
or Euclidean/Pi norm identification is assumed. Source: original real coefficients. -/
theorem incrementsMeanRealCoordinate_norm_le : ‖incrementsMeanRealCoordinate‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
  intro a
  exact Complex.abs_re_le_norm z

/-- Native linear postcomposition bounds each actual real coefficient jet.
Source: application of the existing complex coefficient bound to its real part. -/
theorem incrementsMeanRealCoordinate_jet_le
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : D → ℂ) (x : D) (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ incrementsMeanRealCoordinate (f y)) x‖ ≤
      ‖iteratedFDeriv ℝ k f x‖ := by
  rw [show (fun y ↦ incrementsMeanRealCoordinate (f y)) =
    incrementsMeanRealCoordinate ∘ f from rfl,
    incrementsMeanRealCoordinate.iteratedFDeriv_comp_left hf (by simp)]
  exact (incrementsMeanRealCoordinate.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_of_le_one_left (norm_nonneg _) incrementsMeanRealCoordinate_norm_le)


variable {Λ I : Type*} [Fintype Λ] [Fintype I] {N : ℕ}

/-- Smoothness of the actual coefficient remainder follows from its original
finite bilinear expression; no smooth mean is supplied as an input. -/
theorem incrementsMeanRemainder_contDiffOn
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (O : Set D)
    (L E : D → Λ → I → Fin N → ℂ)
    (hL : ContDiffOn ℝ ∞ L O) (hE : ContDiffOn ℝ ∞ E O) (i j : I) :
    ContDiffOn ℝ ∞ (fun y ↦ incrementsMeanRemainder (L y) (E y) i j) O := by
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  have he : (fun y ↦ incrementsMeanRemainder (L y) (E y) i j) =
      fun y ↦ B (L y) (E y) + B (E y) (L y) + B (E y) (E y) := by
    funext y
    exact incrementsMeanRemainder_eq (L y) (E y) i j
  rw [he]
  exact (((B.contDiff.comp_contDiffOn hL).clm_apply hE).add
    ((B.contDiff.comp_contDiffOn hE).clm_apply hL)).add
      ((B.contDiff.comp_contDiffOn hE).clm_apply hE)

/-- Literal base0 paper norm of the actual REAL mean-remainder component.
The output is genuinely finite before toReal, and chart aggregation is MAX.
Actual leading/error coefficient estimates remain original upstream obligations;
no desired mean bound is a premise. Source: original main.tex645–661. -/
theorem incrementsMeanRemainder_paper_size
    {ι : Type*} [Fintype ι] {n : ℕ} (order : ℕ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ a, IsOpen (O a)) (hSO : ∀ a, S a ⊆ O a)
    (L E : ι → (Fin n → ℝ) → Λ → I → Fin N → ℂ)
    (hL : ∀ a, ContDiffOn ℝ ∞ (L a) (O a))
    (hE : ∀ a, ContDiffOn ℝ ∞ (E a) (O a)) (i j : I)
    (ell M epsilon : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hLb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (L a) x‖ ≤ M)
    (hEb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (E a) x‖ ≤ M * epsilon) :
    let g := fun a x ↦ incrementsMeanRealCoordinate (incrementsMeanRemainder (L a x) (E a x) i j)
    paperAtlasWeighted 0 order ell g O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 order ell g O S).toReal ≤
        ((order + 1 : ℕ) : ℝ) * ((∑ a ∈ Finset.range (order + 1), ((a + 1 : ℕ) : ℝ)) *
          (3 * ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ * 2 ^ order * M ^ 2 * epsilon)) := by
  let r := fun a x ↦ incrementsMeanRemainder (L a x) (E a x) i j
  let g := fun a x ↦ incrementsMeanRealCoordinate (r a x)
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  let T := 3 * ‖B‖ * 2 ^ order * M ^ 2 * epsilon
  let Rsum := (∑ a ∈ Finset.range (order + 1), ((a + 1 : ℕ) : ℝ)) * T
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hRsum : 0 ≤ Rsum := by dsimp [Rsum]; positivity
  have hrs : ∀ a, ContDiffOn ℝ ∞ (r a) (O a) :=
    fun a ↦ incrementsMeanRemainder_contDiffOn (O a) (L a) (E a) (hL a) (hE a) i j
  have hgs : ∀ a, ContDiffOn ℝ ∞ (g a) (O a) :=
    fun a ↦ incrementsMeanRealCoordinate.contDiff.comp_contDiffOn (hrs a)
  have hgb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (g a) x‖ ≤ T := by
    intro a k hk x hx
    have hp := incrementsMeanRealCoordinate_jet_le (r a) x
      ((hrs a).contDiffAt ((hO a).mem_nhds (hSO a hx))) k
    have hr := incrementsMeanRemainder_scaled_jet (O a) (hO a) (L a) (E a)
      (hL a) (hE a) i j k ell M epsilon hell.le hM hepsilon hepsilon1 (hSO a hx)
      (fun v hv ↦ hLb a v (hv.trans hk) x hx)
      (fun v hv ↦ hEb a v (hv.trans hk) x hx)
    refine ((mul_le_mul_of_nonneg_left hp (pow_nonneg hell.le k)).trans hr).trans ?_
    dsimp [T, B]
    gcongr; norm_num
  have he (a : ι) := scaled_finiteCj_sum_le order (g a) (S a) ell T hell hell1 hT (hgb a)
  have hgf : ∀ a, ∀ k ≤ order,
      BddAbove (Set.range fun x : S a ↦ ‖iteratedFDeriv ℝ k (g a) x‖) := fun a ↦ (he a).1
  have hfinite := paperAtlasWeighted_ne_top 0 order ell g O S hO hSO hgs
    (by simpa using hgf)
  have hprofile : ∀ a ≤ order, ∀ c, finiteCjNorm a (g c) (S c) ≤ Rsum / ell ^ a := by
    intro a ha c
    apply (le_div_iff₀ (pow_pos hell a)).2
    have ht : ell ^ a * finiteCjNorm a (g c) (S c) ≤
        ∑ b ∈ Finset.range (order + 1), ell ^ b * finiteCjNorm b (g c) (S c) := by
      apply Finset.single_le_sum (f := fun b ↦ ell ^ b * finiteCjNorm b (g c) (S c))
      · intro b hb
        exact mul_nonneg (pow_nonneg hell.le b)
          (finiteCjNorm_specification b (g c) (S c)
            (fun k hk ↦ hgf c k (hk.trans (by simpa using hb)))).1
      · simpa using ha
    simpa only [mul_comm] using ht.trans (he c).2
  have hout := paperAtlasWeighted_le_of_finiteCjNorm_bound 0 order ell hell
    g O S hO hSO hgs (by simpa using hgf) (fun a ↦ Rsum / ell ^ a)
    (fun a _ ↦ by positivity) (by simpa using hprofile)
  have hsum : (∑ a ∈ Finset.range (order + 1), ell ^ a * (Rsum / ell ^ a)) =
      ((order + 1 : ℕ) : ℝ) * Rsum := by
    calc
      _ = ∑ a ∈ Finset.range (order + 1), Rsum := by
        apply Finset.sum_congr rfl
        intro a ha
        field_simp [pow_ne_zero a hell.ne']
      _ = _ := by simp
  refine ⟨hfinite, ?_⟩
  simpa only [hsum, Rsum, T, B] using hout


/-- Literal base0 paper norm of the SAME actual two-input coefficient difference.
The actual error difference retains epsilon and the SAME Delta/finite loss. No desired
mean difference estimate is assumed. Source: original equation(6.3). -/
theorem incrementsMeanRemainder_paper_difference
    {ι : Type*} [Fintype ι] {n : ℕ} (order : ℕ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ a, IsOpen (O a)) (hSO : ∀ a, S a ⊆ O a)
    (L E Lbar Ebar : ι → (Fin n → ℝ) → Λ → I → Fin N → ℂ)
    (hL : ∀ a, ContDiffOn ℝ ∞ (L a) (O a))
    (hE : ∀ a, ContDiffOn ℝ ∞ (E a) (O a))
    (hLbar : ∀ a, ContDiffOn ℝ ∞ (Lbar a) (O a))
    (hEbar : ∀ a, ContDiffOn ℝ ∞ (Ebar a) (O a)) (i j : I)
    (ell M epsilon Delta : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hDelta : 0 ≤ Delta)
    (hLb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (L a) x‖ ≤ M)
    (hEb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (E a) x‖ ≤ M * epsilon)
    (hLbarb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (Lbar a) x‖ ≤ M)
    (hEbarb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (Ebar a) x‖ ≤ M * epsilon)
    (hLdiff : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (L a - Lbar a) x‖ ≤ M * Delta)
    (hEdiff : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (E a - Ebar a) x‖ ≤ M * epsilon * Delta) :
    let g := fun a x ↦ incrementsMeanRealCoordinate
      (incrementsMeanRemainder (L a x) (E a x) i j -
        incrementsMeanRemainder (Lbar a x) (Ebar a x) i j)
    paperAtlasWeighted 0 order ell g O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 order ell g O S).toReal ≤
        ((order + 1 : ℕ) : ℝ) * ((∑ a ∈ Finset.range (order + 1), ((a + 1 : ℕ) : ℝ)) *
          (6 * ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ *
            2 ^ order * M ^ 2 * epsilon * Delta)) := by
  let r := fun a x ↦ incrementsMeanRemainder (L a x) (E a x) i j -
    incrementsMeanRemainder (Lbar a x) (Ebar a x) i j
  let g := fun a x ↦ incrementsMeanRealCoordinate (r a x)
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  let T := 6 * ‖B‖ * 2 ^ order * M ^ 2 * epsilon * Delta
  let Rsum := (∑ a ∈ Finset.range (order + 1), ((a + 1 : ℕ) : ℝ)) * T
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hRsum : 0 ≤ Rsum := by dsimp [Rsum]; positivity
  have hrs : ∀ a, ContDiffOn ℝ ∞ (r a) (O a) :=
    fun a ↦ (incrementsMeanRemainder_contDiffOn (O a) (L a) (E a) (hL a) (hE a) i j).sub
      (incrementsMeanRemainder_contDiffOn (O a) (Lbar a) (Ebar a) (hLbar a) (hEbar a) i j)
  have hgs : ∀ a, ContDiffOn ℝ ∞ (g a) (O a) :=
    fun a ↦ incrementsMeanRealCoordinate.contDiff.comp_contDiffOn (hrs a)
  have hgb : ∀ a, ∀ k ≤ order, ∀ x ∈ S a,
      ell ^ k * ‖iteratedFDeriv ℝ k (g a) x‖ ≤ T := by
    intro a k hk x hx
    have hp := incrementsMeanRealCoordinate_jet_le (r a) x
      ((hrs a).contDiffAt ((hO a).mem_nhds (hSO a hx))) k
    have hr := incrementsMeanRemainder_difference_scaled_jet (O a) (hO a)
      (L a) (E a) (Lbar a) (Ebar a) (hL a) (hE a) (hLbar a) (hEbar a)
      i j k ell M epsilon Delta hell.le hM hepsilon hepsilon1 hDelta (hSO a hx)
      (fun v hv ↦ hLb a v (hv.trans hk) x hx)
      (fun v hv ↦ hEbarb a v (hv.trans hk) x hx)
      (fun v hv ↦ hLbarb a v (hv.trans hk) x hx)
      (fun v hv ↦ hEb a v (hv.trans hk) x hx)
      (fun v hv ↦ hLdiff a v (hv.trans hk) x hx)
      (fun v hv ↦ hEdiff a v (hv.trans hk) x hx)
    refine ((mul_le_mul_of_nonneg_left hp (pow_nonneg hell.le k)).trans hr).trans ?_
    dsimp [T, B]
    gcongr; norm_num
  have he (a : ι) := scaled_finiteCj_sum_le order (g a) (S a) ell T hell hell1 hT (hgb a)
  have hgf : ∀ a, ∀ k ≤ order,
      BddAbove (Set.range fun x : S a ↦ ‖iteratedFDeriv ℝ k (g a) x‖) := fun a ↦ (he a).1
  have hfinite := paperAtlasWeighted_ne_top 0 order ell g O S hO hSO hgs
    (by simpa using hgf)
  have hprofile : ∀ a ≤ order, ∀ c, finiteCjNorm a (g c) (S c) ≤ Rsum / ell ^ a := by
    intro a ha c
    apply (le_div_iff₀ (pow_pos hell a)).2
    have ht : ell ^ a * finiteCjNorm a (g c) (S c) ≤
        ∑ b ∈ Finset.range (order + 1), ell ^ b * finiteCjNorm b (g c) (S c) := by
      apply Finset.single_le_sum (f := fun b ↦ ell ^ b * finiteCjNorm b (g c) (S c))
      · intro b hb
        exact mul_nonneg (pow_nonneg hell.le b)
          (finiteCjNorm_specification b (g c) (S c)
            (fun k hk ↦ hgf c k (hk.trans (by simpa using hb)))).1
      · simpa using ha
    simpa only [mul_comm] using ht.trans (he c).2
  have hout := paperAtlasWeighted_le_of_finiteCjNorm_bound 0 order ell hell
    g O S hO hSO hgs (by simpa using hgf) (fun a ↦ Rsum / ell ^ a)
    (fun a _ ↦ by positivity) (by simpa using hprofile)
  have hsum : (∑ a ∈ Finset.range (order + 1), ell ^ a * (Rsum / ell ^ a)) =
      ((order + 1 : ℕ) : ℝ) * Rsum := by
    calc
      _ = ∑ a ∈ Finset.range (order + 1), Rsum := by
        apply Finset.sum_congr rfl
        intro a ha
        field_simp [pow_ne_zero a hell.ne']
      _ = _ := by simp
  refine ⟨hfinite, ?_⟩
  simpa only [hsum, Rsum, T, B] using hout

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsMeanRealCoordinate
#print axioms GlobalEmbedding.Paper.incrementsMeanRealCoordinate_jet_le
#print axioms GlobalEmbedding.Paper.incrementsMeanRealCoordinate_norm_le
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_contDiffOn
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_paper_difference
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_paper_size
