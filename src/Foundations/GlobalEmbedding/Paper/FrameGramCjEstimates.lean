import GlobalEmbedding.Paper.OperatorCompositionCjBound
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, line822, quantitative Gram operator comparison. -/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Uniform Cj bounds for actual frame Gram operators and their difference, with
exact adjoints and actual finite derivative suprema. No injectivity is required.

Proof: real adjoint is an isometry, preserving all derivative norms. Apply the
bilinear composition bound and expand the Gram difference into two terms with one
frame-difference factor. Establish boundedness before taking each actual supremum.
Source: `prop:initialization` proof, line822. Empty U/zero spaces are included. -/
theorem frame_gram_cj_estimates
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (j : ℕ) (U : Set D) (hU : IsOpen U) (A B : D → E →L[ℝ] F)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (L : ℝ) (hL : 0 ≤ L)
    (hAb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k A x‖ ≤ L)
    (hBb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k B x‖ ≤ L) :
    let AA : D → F →L[ℝ] E := fun x ↦ (A x).adjoint
    let BB : D → F →L[ℝ] E := fun x ↦ (B x).adjoint
    let P : D → E →L[ℝ] E := fun x ↦ (AA x).comp (A x)
    let Q : D → E →L[ℝ] E := fun x ↦ (BB x).comp (B x)
    let δ := finiteCjNorm j (A - B) U
    ContDiffOn ℝ ∞ AA U ∧ ContDiffOn ℝ ∞ BB U ∧
    ContDiffOn ℝ ∞ P U ∧ ContDiffOn ℝ ∞ Q U ∧
    (∀ k ≤ j, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ k AA x‖ ≤ L ∧ ‖iteratedFDeriv ℝ k BB x‖ ≤ L ∧
      ‖iteratedFDeriv ℝ k P x‖ ≤ 2 ^ j * L ^ 2 ∧
      ‖iteratedFDeriv ℝ k Q x‖ ≤ 2 ^ j * L ^ 2) ∧
    (∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k (A - B) x‖)) ∧
    0 ≤ δ ∧
    (∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (P - Q) x‖ ≤ 2 * 2 ^ j * L * δ) ∧
    (∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k (P - Q) x‖)) ∧
    finiteCjNorm j (P - Q) U ≤ (j + 1 : ℝ) * (2 * 2 ^ j * L) * δ := by
  let adj := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)
  let AA : D → F →L[ℝ] E := fun x ↦ (A x).adjoint
  let BB : D → F →L[ℝ] E := fun x ↦ (B x).adjoint
  let P : D → E →L[ℝ] E := fun x ↦ (AA x).comp (A x)
  let Q : D → E →L[ℝ] E := fun x ↦ (BB x).comp (B x)
  let δ := finiteCjNorm j (A - B) U
  have hAA : ContDiffOn ℝ ∞ AA U := adj.contDiff.comp_contDiffOn hA
  have hBB : ContDiffOn ℝ ∞ BB U := adj.contDiff.comp_contDiffOn hB
  have hP : ContDiffOn ℝ ∞ P U := hAA.clm_comp hA
  have hQ : ContDiffOn ℝ ∞ Q U := hBB.clm_comp hB
  have hAAb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k AA x‖ ≤ L := by
    intro k hk x hx
    have he := adj.norm_iteratedFDeriv_comp_left A x k
    have heq : ‖iteratedFDeriv ℝ k AA x‖ = ‖iteratedFDeriv ℝ k A x‖ := by
      simpa only [Function.comp_def] using he
    exact heq.le.trans (hAb k hk x hx)
  have hBBb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k BB x‖ ≤ L := by
    intro k hk x hx
    have he := adj.norm_iteratedFDeriv_comp_left B x k
    have heq : ‖iteratedFDeriv ℝ k BB x‖ = ‖iteratedFDeriv ℝ k B x‖ := by
      simpa only [Function.comp_def] using he
    exact heq.le.trans (hBb k hk x hx)
  have hPb := (operator_composition_cj_bound j U hU AA A P hAA hA L L hL hL
    hAAb hAb (fun _ _ ↦ rfl)).1
  have hQb := (operator_composition_cj_bound j U hU BB B Q hBB hB L L hL hL
    hBBb hBb (fun _ _ ↦ rfl)).1
  have hGram : ∀ k ≤ j, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ k P x‖ ≤ 2 ^ j * L ^ 2 ∧
      ‖iteratedFDeriv ℝ k Q x‖ ≤ 2 ^ j * L ^ 2 := by
    intro k hk x hx
    have he : 2 ^ k * L * L ≤ 2 ^ j * L ^ 2 := by
      calc
        _ = 2 ^ k * L ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (sq_nonneg L)
    exact ⟨(hPb k hk x hx).trans he, (hQb k hk x hx).trans he⟩
  have hdiff : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (A - B) x‖ ≤ 2 * L := by
    intro k hk x hx
    rw [iteratedFDeriv_sub_apply ((hA.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
      ((hB.contDiffAt (hU.mem_nhds hx)).of_le (by simp))]
    have h1 := hAb k hk x hx
    have h2 := hBb k hk x hx
    exact (norm_sub_le _ _).trans (by linarith)
  have hdn : ∀ k ≤ j,
      BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k (A - B) x‖) := by
    intro k hk
    exact ⟨2 * L, by rintro _ ⟨x, rfl⟩; exact hdiff k hk x x.property⟩
  have hdSpec := finiteCjNorm_specification j (A - B) U hdn
  have hδ : 0 ≤ δ := hdSpec.1
  have hd : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (A - B) x‖ ≤ δ := hdSpec.2.1
  have hAdjDiff : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (AA - BB) x‖ ≤ δ := by
    intro k hk x hx
    have hfun : AA - BB = adj ∘ (A - B) := by
      funext y
      exact (adj.map_sub (A y) (B y)).symm
    rw [hfun, adj.norm_iteratedFDeriv_comp_left]
    exact hd k hk x hx
  let V1 := fun x ↦ ((AA - BB) x).comp (A x)
  let V2 := fun x ↦ (BB x).comp ((A - B) x)
  have hV1 : ContDiffOn ℝ ∞ V1 U := (hAA.sub hBB).clm_comp hA
  have hV2 : ContDiffOn ℝ ∞ V2 U := hBB.clm_comp (hA.sub hB)
  have hV1b := (operator_composition_cj_bound j U hU (AA - BB) A V1
    (hAA.sub hBB) hA δ L hdSpec.1 hL hAdjDiff hAb (fun _ _ ↦ rfl)).1
  have hV2b := (operator_composition_cj_bound j U hU BB (A - B) V2
    hBB (hA.sub hB) L δ hL hdSpec.1 hBBb hd (fun _ _ ↦ rfl)).1
  have hId : P - Q = V1 + V2 := by
    funext x
    ext v
    simp only [P, Q, V1, V2, Pi.add_apply, Pi.sub_apply,
      sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  have hPQ : ∀ k ≤ j, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ k (P - Q) x‖ ≤ 2 * 2 ^ j * L * δ := by
    intro k hk x hx
    rw [hId, iteratedFDeriv_add_apply
      ((hV1.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
      ((hV2.contDiffAt (hU.mem_nhds hx)).of_le (by simp))]
    have h1 := hV1b k hk x hx
    have h2 := hV2b k hk x hx
    have hp : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk
    have hmul := mul_le_mul_of_nonneg_right hp (mul_nonneg hL hdSpec.1)
    exact (norm_add_le _ _).trans (by nlinarith)
  have hPQn : ∀ k ≤ j,
      BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k (P - Q) x‖) := by
    intro k hk
    exact ⟨2 * 2 ^ j * L * δ,
      by rintro _ ⟨x, rfl⟩; exact hPQ k hk x x.property⟩
  have hnorm : finiteCjNorm j (P - Q) U ≤ (j + 1 : ℝ) * (2 * 2 ^ j * L) * δ := by
    have he := (finiteCjNorm_specification j (P - Q) U hPQn).2.2.1
      (fun _ ↦ 2 * 2 ^ j * L * δ) (by intros; positivity) hPQ
    simpa [mul_assoc] using he
  exact ⟨hAA, hBB, hP, hQ,
    (fun k hk x hx ↦ ⟨hAAb k hk x hx, hBBb k hk x hx, hGram k hk x hx⟩),
    hdn, hdSpec.1, hPQ, hPQn, hnorm⟩

end GlobalEmbedding.Paper
