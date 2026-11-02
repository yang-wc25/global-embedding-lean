import GlobalEmbedding.Paper.FreeHopfBalancedCorrection
import GlobalEmbedding.Paper.FreeHopfCorrectionStability

/-!
# Final same-map selector assembly from the genuine normalized inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines477–495.
DAG: `free-selector-from-normalized-inverse`; exclusive worker W6.
The actual balanced construction is invoked once; its U is retained everywhere.
-/

noncomputable section
open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual normalized inverse and actual patch margins turn one original
residual family into the full original selector conclusion in its exact dimension.
Construct U once by the genuine whole-product balanced theorem. Apply genuine
Hopf rank stability to that same U on the intersection of the correction and rank
intervals, retaining its true C² constant. At a common positive parameter, the
same corrected map has exact Gram I and all free columns independent. Its actual
native smooth ordered cofactor provides one global unit complement. No corrected
map, rank or normal is assumed. The inverse and margins are honest intermediate
outputs of the separately owned actual normalized-column construction, not new
hypotheses of the original free target. Source: lines477–495. -/
theorem freeHopf_selector_from_normalized_inverse {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (J : Set ℝ) (hJ : IsOpen J) (hzero : 0 ∈ J)
    (P : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hP : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞ P (J ×ˢ univ))
    (S3 S4 : FreeHopfProduct C → Matrix (Fin a) (Fin a) ℝ)
    (hresidual : ∀ (ε : ℝ), ε ∈ J → ∀ x : FreeHopfProduct C,
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (fun y ↦ P (ε, y)) x) =
        1 + ε ^ 3 • S3 x + ε ^ 4 • S4 x)
    (A : ℝ → FreeHopfProduct C → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hA : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : FreeHopfProduct C,
      IsBalancedPairingRightInverse (fun y ↦ P (ε, y)) (freeHopfGenerator C) x (A ε x))
    (Atilde : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hAtilde : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞ Atilde (J ×ˢ univ))
    (hscale : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : FreeHopfProduct C,
      Atilde (ε, x) = ε • A ε x)
    {Patch : Type*} {μ εbar : ℝ} (hμ : 0 < μ) (hbar : 0 < εbar)
    (K : Patch → Set (FreeHopfProduct C)) (hcover : ∀ x, ∃ p, x ∈ K p)
    (prj : Patch → FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (masked : Patch → BalancedPairingIndex a → Bool)
    (hprj : ∀ p x, x ∈ K p → ‖prj p x‖ ≤ 1)
    (hmargin : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p → ∀ u,
      μ * ‖u‖ ≤ ‖freeColumnOperator
        (freeNormalizedColumns (prj p x) (masked p) ε
          (freeFlowColumns (freeHopfProductFlow C) (fun y ↦ P (ε, y)) x)) u‖) :
    ∃ F ν : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)),
      FreeSelectorProperties (freeHopfModel C) (freeHopfProductFlow C) F ν := by
  obtain ⟨δ, hδ, hδJ, B, hB, U, hU, hspec⟩ :=
    freeHopf_balanced_correction C J hJ hzero P hP S3 S4 hresidual
      A hA Atilde hAtilde hscale
  have htime {ε : ℝ} (hε : 0 < ε) (hb : ε < min εbar δ) :
      ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using
      (lt_of_lt_of_le hb (min_le_right εbar δ))
  have hPs (ε : ℝ) (hε : 0 < ε) (hb : ε < min εbar δ) :
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞
        (fun y ↦ P (ε, y)) :=
    hP.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y ↦ ⟨hδJ (htime hε hb), mem_univ y⟩)
  have hUs (ε : ℝ) (hε : 0 < ε) (hb : ε < min εbar δ) :
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ∞
        (fun y ↦ U (ε, y)) :=
    hU.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y ↦ ⟨htime hε hb, mem_univ y⟩)
  obtain ⟨ε₀, hε₀, hsmall, hstable⟩ := freeHopf_correction_rank_stability C
    (fun ε y ↦ P (ε, y)) (fun ε y ↦ U (ε, y)) hPs hUs K hcover prj masked hprj
    hB.le hμ (lt_min hbar hδ)
    (fun ε hε hb _ x _ ↦ (hspec ε (htime hε hb) x).2)
    (fun ε hε hb ↦ hmargin ε hε (lt_of_lt_of_le hb (min_le_left εbar δ)))
  let ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hεsmall : ε < ε₀ := half_lt_self hε₀
  have hb : ε < min εbar δ := lt_of_lt_of_le hεsmall hsmall
  let F := fun y ↦ P (ε, y) + U (ε, y)
  have hF := (hPs ε hε hb).add (hUs ε hε hb)
  obtain ⟨ν, hν⟩ := freeHopf_selector_properties_of_gram_free C F hF
    (fun x ↦ (hspec ε (htime hε hb) x).1) (hstable ε hε hεsmall)
  exact ⟨F, ν, hν⟩

#print axioms freeHopf_selector_from_normalized_inverse

end GlobalEmbedding.Paper
