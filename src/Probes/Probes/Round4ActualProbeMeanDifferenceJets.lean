import GlobalEmbedding.Paper.IncrementsMeanQuadraticRemainder
import Probes.ActualIncrementJointDirectionalJets

/-!
# Exact quadratic two-parameter difference of the actual opposite mean

The original conjugate-pair mean, with both orderings and its factor 1/4,
is polarized without discarding any reconstruction terms. The resulting
weighted spatial/auxiliary-jet bound has the required (|u|+|v|)|u-v| form
when the actual coefficient budgets are supplied by their producer.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {X Λ J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype Λ] [Fintype J] {N : ℕ}
local notation "Coeffs" => Λ → J → Fin N → ℂ

theorem round4_opposite_mean_difference_slow_jets
    (DU DV : X → Coeffs) (i j : J) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hDU : ContDiffOn ℝ ∞ DU O) (hDV : ContDiffOn ℝ ∞ DV O)
    (order : ℕ) (ell K A B E : ℝ) (hell : 0 ≤ ell)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hUb : ∀ k ≤ order, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k DU x‖ ≤ K*A)
    (hVb : ∀ k ≤ order, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k DV x‖ ≤ K*B)
    (hDb : ∀ k ≤ order, ∀ x ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (fun y => DU y-DV y) x‖ ≤ K*E) :
    let meanDiff := fun x => incrementsOppositePrimaryContribution (DU x) i j -
      incrementsOppositePrimaryContribution (DV x) i j
    ContDiffOn ℝ ∞ meanDiff O ∧ ∀ k ≤ order, ∀ x ∈ S,
      ell^k*‖iteratedFDeriv ℝ k meanDiff x‖ ≤
        (2^order*‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖*K^2)*(A+B)*E := by
  intro meanDiff
  let L := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  let DD := fun x => DU x-DV x
  let T1 := fun x => L (DD x) (DU x)
  let T2 := fun x => L (DV x) (DD x)
  have hDD : ContDiffOn ℝ ∞ DD O := hDU.sub hDV
  have hT1 : ContDiffOn ℝ ∞ T1 O := (L.contDiff.comp_contDiffOn hDD).clm_apply hDU
  have hT2 : ContDiffOn ℝ ∞ T2 O := (L.contDiff.comp_contDiffOn hDV).clm_apply hDD
  have heq : meanDiff = fun x => T1 x+T2 x := by
    funext x
    dsimp only [meanDiff,T1,T2,DD]
    rw [← incrementsMeanBilinear_diagonal,← incrementsMeanBilinear_diagonal]
    change L (DU x) (DU x)-L (DV x) (DV x) = _
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  refine ⟨hT1.add hT2,?_⟩
  intro k hk x hx
  have h1 := slow_bilinear_jet_bound_norm L O hO DD DU hDD hDU k ell (K*E) (K*A) hell x (hSO hx)
    (fun a ha => hDb a (ha.trans hk) x hx) (fun a ha => hUb a (ha.trans hk) x hx)
  have h2 := slow_bilinear_jet_bound_norm L O hO DV DD hDV hDD k ell (K*B) (K*E) hell x (hSO hx)
    (fun a ha => hVb a (ha.trans hk) x hx) (fun a ha => hDb a (ha.trans hk) x hx)
  have hsum := actual_joint_slow_add_jet_bound T1 T2 k ell _ _ hell x
    ((hT1.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))
    ((hT2.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp)) h1 h2
  calc
    _ ≤ _ := hsum
    _ = (2^k*‖L‖*K^2)*(A+B)*E := by ring
    _ ≤ _ := by gcongr; norm_num

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_opposite_mean_difference_slow_jets
