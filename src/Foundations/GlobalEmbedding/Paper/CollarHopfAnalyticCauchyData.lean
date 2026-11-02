import GlobalEmbedding.Targets.FreeSelectors
import GlobalEmbedding.Paper.CollarHopfGlobalAnalyticSeed
import GlobalEmbedding.Paper.CollarAnalyticUnitNormal

/-!
# The original global analytic collar Cauchy data

Source: `main.tex`, Proposition `prop:collar`, lines 534–540.
W4 owns global original-input assembly and initial square independence. The actual
chart-jet identification and local square inverse are owned by W5, outside this file.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The SAME canonical normal completes the original free columns in normal-first order.
This is only finite reindexing of the accepted actual ordered-cofactor completion. -/
theorem collarHopf_initial_square_columns_linearIndependent {a : ℕ} (C : Fin a → ℕ)
    (H ν : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x))
    (hν : ∀ x, ν x = freeOrderedUnitComplement (freeSymmetricColumnCount a + a)
      (fun i ↦ freeFlowColumns (freeHopfProductFlow C) H x
        ((freeCofactorColumnOrder a).symm i))) :
    ∀ x, LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν x) (freeFlowColumns (freeHopfProductFlow C) H x)) := by
  intro x
  let d := freeSymmetricColumnCount a + a
  let v := fun i : Fin d ↦ freeFlowColumns (freeHopfProductFlow C) H x
    ((freeCofactorColumnOrder a).symm i)
  have hv : LinearIndependent ℝ v :=
    (hfree x).comp _ (freeCofactorColumnOrder a).symm.injective
  let e : Unit ⊕ BalancedPairingIndex a → Fin (d + 1) :=
    Sum.elim (fun _ ↦ Fin.last d) (fun k ↦ (freeCofactorColumnOrder a k).castSucc)
  have he : Function.Injective e := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Subsingleton.elim i j)
    · have hh := congrArg Fin.val hij
      have hl := (freeCofactorColumnOrder a j).isLt
      change (freeSymmetricColumnCount a + a) = (freeCofactorColumnOrder a j).val at hh
      omega
    · have hh := congrArg Fin.val hij
      have hl := (freeCofactorColumnOrder a i).isLt
      change (freeCofactorColumnOrder a i).val = (freeSymmetricColumnCount a + a) at hh
      omega
    · apply congrArg Sum.inr
      apply (freeCofactorColumnOrder a).injective
      change (freeCofactorColumnOrder a i).castSucc =
        (freeCofactorColumnOrder a j).castSucc at hij
      exact Fin.castSucc_inj.mp hij
  have hs := (freeOrderedUnitComplement_linearIndependent d v hv).comp e he
  have hf : (Fin.snoc v (freeOrderedUnitComplement d v)) ∘ e =
      Sum.elim (fun _ : Unit ↦ ν x) (freeFlowColumns (freeHopfProductFlow C) H x) := by
    funext k
    cases k with
    | inl k => simp [e, hν x, d, v]
    | inr k => simp [e, v]
  exact hf ▸ hs

/-- Only the original m/hm/C/hC data construct the full global analytic Cauchy data.

Proof: use the accepted full original free-selector theorem once to obtain the original
smooth identity-Gram free H0 in exactly s_m+m+1 dimensions. Apply the accepted global
analytic exact seed once, then the accepted actual analytic unit normal once. The preceding
finite reindexing of actual cofactor completion gives the genuine initial square family.
No desired H, normal, initial rank, inverse, chart or CK solution is assumed.
Source: Proposition prop:collar, main.tex534–540. -/
theorem collarHopf_analytic_cauchy_data (m : ℕ) (hm : 1 ≤ m)
    (C : Fin m → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    ∃ H ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1)),
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1))) ω H ∧
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1))) ω ν ∧
      (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H x) = 1) ∧
      (∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x)) ∧
      (∀ x, ν x = freeOrderedUnitComplement (freeSymmetricColumnCount m + m)
        (fun i ↦ freeFlowColumns (freeHopfProductFlow C) H x
          ((freeCofactorColumnOrder m).symm i))) ∧
      (∀ x, ‖ν x‖ = 1) ∧
      (∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) H x k) = 0) ∧
      ∀ x, LinearIndependent ℝ
        (Sum.elim (fun _ : Unit ↦ ν x) (freeFlowColumns (freeHopfProductFlow C) H x)) := by
  let _ : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
  obtain ⟨H0, _, hH0⟩ := free_hopf_selectors_with_line_complement m hm C hC
  obtain ⟨H, hH, hmetric, hfree⟩ := collarHopf_global_analytic_seed C H0
    hH0.1 hH0.2.2.2.1 hH0.2.2.1
  obtain ⟨ν, hνeq, hν, hunit, hperp⟩ := collarHopf_analytic_unit_normal C H hH hfree
  exact ⟨H, ν, hH, hν, hmetric, hfree, hνeq, hunit, hperp,
    collarHopf_initial_square_columns_linearIndependent C H ν hfree hνeq⟩

end GlobalEmbedding.Paper
