import GlobalEmbedding.Paper.FreeCorrectionStability
import GlobalEmbedding.Paper.FreeHopfUnitComplements

/-!
# Global correction rank stability for the original Hopf partial columns

Source: `main.tex`, `thm:free`, lines489–495. DAG: `free-hopf-correction-stability`.
The actual native vertical C² estimate applies to the genuine Hopf generators.
The normalized patch columns are the original actual orbit derivatives, and the
same actual correction preserves all of them for one common positive epsilon.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A genuine balanced C²-small correction preserves all actual free Hopf columns globally.
Proof: apply the accepted actual native quantitative stability theorem to the
genuine smooth Hopf generator sections. Identify its native columns with the
original literal orbit columns, including every sorted second derivative. The
same threshold works on every patch, and actual patch coverage gives the whole
product. Neither the corrected rank nor a normalized error bound is an input. -/
theorem freeHopf_correction_rank_stability {a N : ℕ}
    (C : Fin a → ℕ) [∀ i, Fact (0 < C i)] {Patch : Type*}
    {Cbound μ εbar : ℝ}
    (P U : ℝ → FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hP : ∀ ε, 0 < ε → ε < εbar →
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (P ε))
    (hU : ∀ ε, 0 < ε → ε < εbar →
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (U ε))
    (K : Patch → Set (FreeHopfProduct C))
    (hcover : ∀ x, ∃ p, x ∈ K p)
    (prj : Patch → FreeHopfProduct C →
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (masked : Patch → BalancedPairingIndex a → Bool)
    (hprj : ∀ p x, x ∈ K p → ‖prj p x‖ ≤ 1)
    (hC : 0 ≤ Cbound) (hμ : 0 < μ) (hbar : 0 < εbar)
    (hbound : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p →
      balancedVerticalC2Size (freeHopfGenerator C) (U ε) x ≤ Cbound * ε ^ 2)
    (hmargin : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p → ∀ u,
      μ * ‖u‖ ≤ ‖freeColumnOperator
        (freeNormalizedColumns (prj p x) (masked p) ε
          (freeFlowColumns (freeHopfProductFlow C) (P ε) x)) u‖) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ εbar ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ x,
      LinearIndependent ℝ
        (freeFlowColumns (freeHopfProductFlow C) (P ε + U ε) x) := by
  have hnative : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p → ∀ u,
      μ * ‖u‖ ≤ ‖freeColumnOperator
        (freeNormalizedColumns (prj p x) (masked p) ε
          (balancedPairingColumns (P ε) (freeHopfGenerator C) x)) u‖ := by
    intro ε hε hb p x hx u
    rw [freeHopf_balanced_pairing_columns C (P ε) (hP ε hε hb) x]
    exact hmargin ε hε hb p x hx u
  obtain ⟨ε₀, hε₀, hε₀bar, hstable⟩ := free_actual_correction_rank_stability
    (freeHopfGeneratorSection C) P U hP hU K prj masked hprj hC hμ hbar hbound hnative
  refine ⟨ε₀, hε₀, hε₀bar, ?_⟩
  intro ε hε hsmall x
  obtain ⟨p, hx⟩ := hcover x
  have hb : ε < εbar := lt_of_lt_of_le hsmall hε₀bar
  have hh := hstable ε hε hsmall p x hx
  change LinearIndependent ℝ
    (balancedPairingColumns (P ε + U ε) (freeHopfGenerator C) x) at hh
  rwa [freeHopf_balanced_pairing_columns C _ ((hP ε hε hb).add (hU ε hε hb)) x] at hh

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_correction_rank_stability
