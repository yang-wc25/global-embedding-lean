import GlobalEmbedding.Paper.SelectorCompactInjectiveBound
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.CollarAmbientHopfSourceCoefficients

/-!
# A fixed actual native free neighborhood on the whole Hopf product

Source: `main.tex`, prop:collar, line522.
DAG: `collar-hopf-native-free-persistence`; W2 first AS2b child.
Reuse the original compact lower bound, column-operator error and lower-bound
perturbation APIs. This does not assume or prove the later ambient C5 comparison.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A fixed actual native smooth free H0 determines positive column-error and
rank margins BEFORE any later approximation is chosen. Actual first/sortedsecond
column differences below that fixed error preserve the SAME original column
independence everywhere and a uniform original Euclidean lower bound.

Proof: native smooth columns give a continuous actual finite-sum column operator.
Use the accepted compact injective lower bound, including the zero column space.
Choose delta from that fixed margin and the original column count. The accepted
component-to-operator error and linear lower-bound perturbation give the result.
No desired perturbed rank, determinant, Holder bound or approximation is assumed.
Source: prop:collar, sufficiently close approximation/freeness persistence, line522. -/
theorem collarHopf_native_free_persistence {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H0 : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH0 : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H0)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H0 x)) :
    ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧
      ∀ H : FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
        (∀ x k, ‖freeFlowColumns (freeHopfProductFlow C) H x k -
          freeFlowColumns (freeHopfProductFlow C) H0 x k‖ ≤ δ) →
        ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x) ∧
          ∀ u : EuclideanSpace ℝ (BalancedPairingIndex a),
            μ * ‖u‖ ≤ ‖freeColumnOperator
              (freeFlowColumns (freeHopfProductFlow C) H x) u‖ := by
  let A := fun x ↦ freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) H0 x)
  have hA : Continuous A := by
    apply continuous_finsetSum Finset.univ
    intro k _
    exact (ContinuousLinearMap.smulRightL ℝ
      (EuclideanSpace ℝ (BalancedPairingIndex a)) (EuclideanSpace ℝ (Fin N))
      (EuclideanSpace.proj k)).continuous.comp
      (freeHopf_free_columns_contMDiff C H0 hH0 k).continuous
  have hinj (x : FreeHopfProduct C) : Function.Injective (A x) :=
    (freeColumnOperator_injective_iff _).mpr (hfree x)
  obtain ⟨ν, hν, hbase⟩ := selector_compact_injective_bound A hA hinj
  let q : ℝ := Fintype.card (BalancedPairingIndex a)
  have hq : 0 ≤ q := by positivity
  let δ := ν / (2 * (q + 1))
  have hδ : 0 < δ := div_pos hν (by positivity)
  have hsmall : q * δ ≤ ν / 2 := by
    have heq : δ * (2 * (q + 1)) = ν := by
      dsimp only [δ]
      exact div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 2 * (q + 1)))
    nlinarith
  refine ⟨δ, ν / 2, hδ, by positivity, ?_⟩
  intro H hclose x
  let B := freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) H x)
  have herr : ‖A x - B‖ ≤ ν / 2 := by
    rw [norm_sub_rev]
    change ‖freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) H x) -
      freeColumnOperator (freeFlowColumns (freeHopfProductFlow C) H0 x)‖ ≤ ν / 2
    rw [← freeColumnOperator_sub]
    exact (freeColumnOperator_norm_le _ hδ.le (hclose x)).trans hsmall
  have hlower (u : EuclideanSpace ℝ (BalancedPairingIndex a)) :
      (ν / 2) * ‖u‖ ≤ ‖B u‖ := by
    have hh := linear_map_lower_bound_perturbation (A x) B ν (ν / 2) (hbase x) herr u
    convert hh using 1
    ring
  have hB : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro u hu
    have hh := hlower u
    rw [hu, norm_zero] at hh
    by_contra hzero
    exact (not_lt_of_ge hh) (mul_pos (by positivity) (norm_pos_iff.mpr hzero))
  exact ⟨(freeColumnOperator_injective_iff _).mp hB, hlower⟩

/-- The SAME fixed H0 column neighborhood gives genuine nonzero full row Gram
determinants for the actual ambient T_F on EVERY original base orbit fiber.
The actual ambient/native column identity discharges the native closeness input;
the accepted whole-fiber determinant theorem then applies. This is not yet a
claim that ambient C5 approximation supplies those actual column errors.
Source: prop:collar, fixed-neighborhood rank persistence, line522. -/
theorem collarHopf_ambient_rank_neighborhood {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H0 : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH0 : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H0)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H0 x)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N),
        (∀ x k, ‖freeFlowColumns (collarAmbientHopfFlow C) F
          (freeHopfAmbientInclusion C x) k -
            freeFlowColumns (freeHopfProductFlow C) H0 x k‖ ≤ δ) →
        ∀ x : FreeHopfProduct C, ∀ y : Fin a → ℝ,
          (collarAmbientHopfPairingMatrix C F
              (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x)) *
            (collarAmbientHopfPairingMatrix C F
              (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x))).transpose).det ≠ 0 := by
  obtain ⟨δ, μ, hδ, _, hstable⟩ := collarHopf_native_free_persistence C H0 hH0 hfree
  refine ⟨δ, hδ, ?_⟩
  intro F hclose x y
  have hnative : ∀ z k, ‖freeFlowColumns (freeHopfProductFlow C)
      (F ∘ freeHopfAmbientInclusion C) z k -
        freeFlowColumns (freeHopfProductFlow C) H0 z k‖ ≤ δ := by
    intro z k
    rw [← collarAmbientHopfColumns_inclusion]
    exact hclose z k
  exact collarAmbientHopfPairingMatrix_fiber_det_ne_zero C F
    (fun z ↦ (hstable (F ∘ freeHopfAmbientInclusion C) hnative z).1) x y

end GlobalEmbedding.Paper
