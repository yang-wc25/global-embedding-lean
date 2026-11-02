import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.FreeGramRightInverse
import GlobalEmbedding.Paper.FreeCorrectionStability
import GlobalEmbedding.Paper.FrameGramCjEstimates
import GlobalEmbedding.Paper.CoerciveInverseBounds
import GlobalEmbedding.Paper.InverseDerivativeBounds
import GlobalEmbedding.Paper.CollarHopfAmbientC5Neighborhood

/-!
# Actual original Hopf Gram right inverse: uniform fiber C3 bounds

Source: `main.tex`, prop:collar, lines522–534.
DAG: `collar-hopf-orbit-gram-jet-bound`; sole AS2b owner W2.
Reuse every accepted generic Gram/inverse/composition estimate directly.
-/

noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual common original-column margins and C3 orbit jets give a common C3
bound for the SAME existing Gram right inverse, chosen BEFORE the observable.

Proof: differentiate the original finite-sum synthesis using fixed smulRightL
maps and their actual norms. Apply the accepted frame-Gram estimate, coercive
inverse theorem, inverse-derivative recurrence, and heterogeneous composition
estimate. Native lower margins give genuine coercivity and the already proved
right-inverse specification. No generic inverse calculus is reproved.
The inputs are supplied by the preceding actual ambient C5 neighborhood theorem;
matching the fixed finite cofactor enumeration and original little norm is later.
Source: actual quantitative inverse in prop:collar, lines522–534. -/
theorem collarHopf_orbit_gram_jet_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (μ L : ℝ) (hμ : 0 < μ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧
      ∀ U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
        ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U →
        (∀ z, ∀ u : EuclideanSpace ℝ (BalancedPairingIndex a),
          μ * ‖u‖ ≤ ‖freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) U z) u‖) →
        (∀ x : FreeHopfProduct C, ∀ y : EuclideanSpace ℝ (Fin a), ∀ n ≤ 3,
          ∀ k : BalancedPairingIndex a,
          ‖iteratedFDeriv ℝ n (fun t : EuclideanSpace ℝ (Fin a) ↦
            freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) k) y‖ ≤ L) →
        ∀ x : FreeHopfProduct C,
        let A := fun t : EuclideanSpace ℝ (Fin a) ↦
          freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t))
        ContDiff ℝ ∞ (fun t ↦ freeGramRightInverse (A t)) ∧
        (∀ t, (A t).adjoint.comp (freeGramRightInverse (A t)) =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (BalancedPairingIndex a))) ∧
        ∀ n ≤ 3, ∀ y : EuclideanSpace ℝ (Fin a),
          ‖iteratedFDeriv ℝ n (fun t ↦ freeGramRightInverse (A t)) y‖ ≤ K := by
  let E := EuclideanSpace ℝ (BalancedPairingIndex a)
  let W := EuclideanSpace ℝ (Fin N)
  let Y := EuclideanSpace ℝ (Fin a)
  let S : BalancedPairingIndex a → W →L[ℝ] E →L[ℝ] W := fun k ↦
    ContinuousLinearMap.smulRightL ℝ E W (EuclideanSpace.proj k)
  let s : ℝ := (∑ k : BalancedPairingIndex a, ‖S k‖) * L
  have hs : 0 ≤ s := mul_nonneg (Finset.sum_nonneg (fun k _ ↦ norm_nonneg (S k))) hL
  let c := μ ^ 2
  have hc : 0 < c := sq_pos_of_pos hμ
  let m := 8 * s ^ 2
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  let R : ℕ → ℝ := Nat.rec (1 + c⁻¹) (fun k r ↦ r + 4 ^ k * r ^ 2 * m)
  let r := |R 3|
  have hr : 0 ≤ r := abs_nonneg _
  let K := 1 + 8 * s * r
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro U hU hlower hcols x
  let v : BalancedPairingIndex a → Y → W := fun k t ↦
    freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) k
  have hv (k : BalancedPairingIndex a) : ContDiff ℝ ∞ (v k) :=
    ((freeHopf_free_columns_contMDiff C U hU k).comp
      (freeHopfOrbitLift_contMDiff C x)).contDiff
  let A : Y → E →L[ℝ] W := fun t ↦ freeColumnOperator (fun k ↦ v k t)
  have hAeq : A = fun t ↦ ∑ k : BalancedPairingIndex a, S k (v k t) := rfl
  have hA : ContDiff ℝ ∞ A := by
    rw [hAeq]
    exact ContDiff.sum (fun k _ ↦ (S k).contDiff.comp (hv k))
  have hAb (n : ℕ) (hn : n ≤ 3) (y : Y) : ‖iteratedFDeriv ℝ n A y‖ ≤ s := by
    rw [hAeq, iteratedFDeriv_fun_sum_apply
      (f := fun k t ↦ S k (v k t))
      (fun k _ ↦ by
        simpa only [Function.comp_def] using
          (((S k).contDiff.comp (hv k)).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)))]
    calc
      _ ≤ ∑ k : BalancedPairingIndex a, ‖iteratedFDeriv ℝ n (fun t ↦ S k (v k t)) y‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k : BalancedPairingIndex a, ‖S k‖ * L := by
        apply Finset.sum_le_sum
        intro k _
        have he := (S k).norm_iteratedFDeriv_comp_left (x := y) (hv k).contDiffAt
          (show (n : ℕ∞ω) ≤ ∞ by simp)
        exact he.trans (mul_le_mul_of_nonneg_left (hcols x y n hn k) (norm_nonneg _))
      _ = s := by rw [← Finset.sum_mul]
  have hinj (t : Y) : Function.Injective (A t) := by
    apply (injective_iff_map_eq_zero (A t)).mpr
    intro u hu
    have he := hlower (freeHopfOrbitLift C x t) u
    change μ * ‖u‖ ≤ ‖A t u‖ at he
    rw [hu, norm_zero] at he
    have hn : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    exact norm_eq_zero.mp hn
  obtain ⟨_, _, hG, _, hGb, _⟩ := frame_gram_cj_estimates 3 univ isOpen_univ A A
    hA.contDiffOn hA.contDiffOn s hs (fun n hn t _ ↦ hAb n hn t)
    (fun n hn t _ ↦ hAb n hn t)
  let G : Y → E →L[ℝ] E := fun t ↦ (A t).adjoint.comp (A t)
  have hcoer (t : Y) (_ht : t ∈ (univ : Set Y)) (u : E) :
      c * ‖u‖ ^ 2 ≤ inner ℝ u (G t u) := by
    change c * ‖u‖ ^ 2 ≤ inner ℝ u ((A t).adjoint (A t u))
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    have he := hlower (freeHopfOrbitLift C x t) u
    change μ * ‖u‖ ≤ ‖A t u‖ at he
    dsimp only [c]
    nlinarith [norm_nonneg (A t u), mul_nonneg hμ.le (norm_nonneg u)]
  obtain ⟨hbase, hinv⟩ := coercive_inverse_smooth_bound univ isOpen_univ G c hc hG hcoer
  have hib : ∀ n ≤ 3, ∀ t : Y, ‖iteratedFDeriv ℝ n (fun t ↦ (G t).inverse) t‖ ≤ r := by
    have he := inverse_derivative_bounds 3 univ isOpen_univ G hG
      (fun t ht ↦ (G t).isUnit_iff_bijective.mpr (hbase t ht).1.bijective)
      c⁻¹ m (by positivity) hm
      (by simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using
        fun t ht ↦ (hbase t ht).2)
      (fun n _ hn t ht ↦ by
        simpa only [G, show (2 : ℝ) ^ 3 = 8 by norm_num] using (hGb n hn t ht).2.2.1)
      R rfl (fun _ ↦ rfl)
    intro n hn t
    have hh := he 3 le_rfl n hn t (mem_univ t)
    rw [ContinuousLinearMap.ringInverse_eq_inverse] at hh
    exact hh.trans (le_abs_self _)
  have hright : ContDiff ℝ ∞ (fun t ↦ freeGramRightInverse (A t)) := by
    have hh := hA.clm_comp (contDiffOn_univ.mp hinv)
    exact hh
  have hprod := (operator_composition_cj_bound 3 univ isOpen_univ A
    (fun t ↦ (G t).inverse) (fun t ↦ freeGramRightInverse (A t))
    hA.contDiffOn hinv s r hs hr (fun n hn t _ ↦ hAb n hn t)
    (fun n hn t _ ↦ hib n hn t) (fun _ _ ↦ rfl)).1
  refine ⟨hright, fun t ↦ freeGramRightInverse_spec (A t) (hinj t), ?_⟩
  intro n hn y
  have he := hprod n hn y (mem_univ y)
  have hp : (2 : ℝ) ^ n ≤ 8 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at hh ⊢
    exact hh
  exact he.trans (by dsimp only [K]; nlinarith [mul_nonneg hs hr,
    mul_le_mul_of_nonneg_right hp (mul_nonneg hs hr)])

/-- A fixed actual smooth ambient extension with free restriction gives a fixed
positive C5 neighborhood and a common genuine Gram right-inverse C3 bound,
BEFORE choosing F. No desired rank, synthesis margin, inverse jet or column jet
bound on F is a premise: the accepted actual C5 neighborhood supplies them.
Proof: invoke that neighborhood once, then apply the actual Gram estimate above
to its original native restriction and true fiber jets. Source: prop:collar522–534. -/
theorem collarHopf_fixed_ambient_c5_gram_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hf0 : ContDiff ℝ ∞ f0)
    (hfree : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (f0 ∘ freeHopfAmbientInclusion C) x)) :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      ∀ F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ F →
        (∀ x : FreeHopfProduct C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i (F - f0) (freeHopfAmbientInclusion C x)‖ ≤ η) →
        ∀ x : FreeHopfProduct C,
        let A := fun t : EuclideanSpace ℝ (Fin a) ↦ freeColumnOperator
          (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C)
            (freeHopfOrbitLift C x t))
        ContDiff ℝ ∞ (fun t ↦ freeGramRightInverse (A t)) ∧
        (∀ t, (A t).adjoint.comp (freeGramRightInverse (A t)) =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (BalancedPairingIndex a))) ∧
        ∀ n ≤ 3, ∀ y : EuclideanSpace ℝ (Fin a),
          ‖iteratedFDeriv ℝ n (fun t ↦ freeGramRightInverse (A t)) y‖ ≤ K := by
  obtain ⟨η, μ, L, hη, hμ, hL, hnear⟩ :=
    collarHopf_fixed_ambient_c5_neighborhood C f0 hf0 hfree
  obtain ⟨K, hK, hb⟩ := collarHopf_orbit_gram_jet_bound C μ L hμ (zero_le_one.trans hL)
  refine ⟨η, K, hη, hK, ?_⟩
  intro F hF hclose
  obtain ⟨hstable, hcols, _⟩ := hnear F hF hclose
  exact hb (F ∘ freeHopfAmbientInclusion C)
    (hF.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C))
    (fun z ↦ (hstable z).2) hcols

end GlobalEmbedding.Paper
