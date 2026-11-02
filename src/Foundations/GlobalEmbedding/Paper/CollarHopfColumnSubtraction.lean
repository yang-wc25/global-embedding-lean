import GlobalEmbedding.Paper.FreeHopfUnitComplements

/-!
# Public reuse of accepted original Hopf column subtraction

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-column-subtraction-reuse`; W2 exact ROOTrequested extraction.
Proof bodies are extracted from accepted4b1a5eb6, not reproved.
See column-subtraction-reuse-provenance.json for bytewise binder mapping.
-/

noncomputable section
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper

/-- Exact accepted local hdsub, promoted with the same explicit native binders.
Proof: the original actual generator/mvfderiv identity and mvfderiv_fun_sub;
the accepted body is unchanged except removing its local indentation.
Source: actual ambient error transfer in prop:collar, lines520–526. -/
theorem freeHopfDeriv_sub {a N : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (P Q : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hQ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Q)
    (i : Fin a) : freeHopfDeriv C i (P - Q) = freeHopfDeriv C i P - freeHopfDeriv C i Q := by
  funext z
  change freeHopfDeriv C i (fun x ↦ P x - Q x) z =
    freeHopfDeriv C i P z - freeHopfDeriv C i Q z
  rw [← freeHopfGenerator_mvfderiv C i _ (hP.sub hQ) z,
    ← freeHopfGenerator_mvfderiv C i P hP z, ← freeHopfGenerator_mvfderiv C i Q hQ z]
  rw [mvfderiv_fun_sub (hP.mdifferentiableAt (by simp)) (hQ.mdifferentiableAt (by simp))]
  rfl

/-- Exact accepted local hcolsub, promoted to all original first/sortedsecond
columns, with only the recorded binder and public derivative-helper substitutions.
Proof: the exact accepted first/second index cases, applying the same first
subtraction identity once/twice to the genuine native smooth first derivatives.
Source: actual C5 error transfer in prop:collar, lines520–526. -/
theorem freeHopf_columns_sub {a N : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (P Q : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hQ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Q)
    (z : FreeHopfProduct C) (k : BalancedPairingIndex a) :
    freeFlowColumns (freeHopfProductFlow C) (P - Q) z k =
      freeFlowColumns (freeHopfProductFlow C) P z k -
        freeFlowColumns (freeHopfProductFlow C) Q z k := by
  cases k with
  | inl i => exact congrFun (freeHopfDeriv_sub C P Q hP hQ i) z
  | inr ij =>
    change freeHopfDeriv C ij.val.1 (freeHopfDeriv C ij.val.2 (P - Q)) z = _
    rw [freeHopfDeriv_sub C P Q hP hQ ij.val.2]
    exact congrFun (freeHopfDeriv_sub C _ _ (freeHopfDeriv_contMDiff C P hP ij.val.2)
      (freeHopfDeriv_contMDiff C Q hQ ij.val.2) ij.val.1) z

end GlobalEmbedding.Paper
