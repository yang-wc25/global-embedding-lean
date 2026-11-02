import GlobalEmbedding.Paper.CollarHopfCompactAmbientExtension
import GlobalEmbedding.Paper.CollarGaussianConvergenceCk

/-!
# Actual Gaussian width choice after a fixed original ambient C5 threshold

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-gaussian-c5-choice`; sole AS2b owner W2.
Reuse actual ALLorder uniform convergence and the genuine CLE jet bound.
No Gaussian approximation estimate or analytic regularity is reproved.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- Every fixed positive original ambient C5 tolerance and width cap admit an
ACTUAL positive normalized Gaussian width giving that genuine global C5 error.
The original ambient keeps its maximum norm and original model; its true CLE
coordinate norms to powers0,...,5 enter a fixed finite factor BEFORE width choice.

Proof: directly use accepted all-order Gaussian uniform jet convergence. Intersect
its six true pointwise estimates with positivity and the requested width cap.
The accepted actual CLE pullback estimate converts them to the original norm.
No inference from an unbounded real conditional supremum is used. The result
asserts accepted Gaussian smoothness; it does not silently turn that into omega.
Source: sufficiently close actual Gaussian approximation, prop:collar520–526. -/
theorem collarHopf_gaussian_ambient_c5_choice {a N : ℕ} (C : Fin a → ℕ)
    (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hf0 : ContDiff ℝ ∞ f0)
    (hcompact0 : HasCompactSupport f0) :
    let d := CollarHopfAmbientDim C
    let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) :=
      f0 ∘ (collarHopfAmbientCoordinates C).symm
    let G : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun ε x ↦
      ∫ y : EuclideanSpace ℝ (Fin d),
        ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • g y
    ∀ τ : ℝ, 0 < τ → ∀ widthCap : ℝ, 0 < widthCap →
      ∃ ε : ℝ, 0 < ε ∧ ε < widthCap ∧
        ContDiff ℝ ∞ (G ε ∘ collarHopfAmbientCoordinates C) ∧
        ∀ p : FreeHopfAmbientSpace C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i ((G ε ∘ collarHopfAmbientCoordinates C) - f0) p‖ ≤ τ := by
  let e := collarHopfAmbientCoordinates C
  let d := CollarHopfAmbientDim C
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := f0 ∘ e.symm
  let G : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun ε x ↦
    ∫ y : EuclideanSpace ℝ (Fin d),
      ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • g y
  have hg : ContDiff ℝ ∞ g := hf0.comp e.symm.contDiff
  have hgc : HasCompactSupport g := hcompact0.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨hreg, hu, _⟩ := collar_gaussian_convergence_Ck g hg hgc
  let S := 1 + ∑ i : Fin 6, ‖e.toContinuousLinearMap‖ ^ i.val
  have hS : 0 < S := by dsimp only [S]; positivity
  have hpow (i : ℕ) (hi : i ≤ 5) : ‖e.toContinuousLinearMap‖ ^ i ≤ S := by
    have hh := Finset.single_le_sum
      (f := fun j : Fin 6 ↦ ‖e.toContinuousLinearMap‖ ^ j.val)
      (fun j _ ↦ pow_nonneg (norm_nonneg _) _)
      (Finset.mem_univ (⟨i, by omega⟩ : Fin 6))
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  change ∀ τ : ℝ, 0 < τ → ∀ widthCap : ℝ, 0 < widthCap →
    ∃ ε : ℝ, 0 < ε ∧ ε < widthCap ∧ ContDiff ℝ ∞ (G ε ∘ e) ∧
      ∀ p : FreeHopfAmbientSpace C, ∀ i ≤ 5,
        ‖iteratedFDeriv ℝ i ((G ε ∘ e) - f0) p‖ ≤ τ
  intro τ hτ widthCap hwidthCap
  let δ := τ / S
  have hδ : 0 < δ := div_pos hτ hS
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i : Fin 6,
      ∀ z : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ i.val (G ε) z - iteratedFDeriv ℝ i.val g z‖ < δ := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [Metric.tendstoUniformly_iff.mp (hu i.val) δ hδ] with ε hclose
    intro z
    have hz := hclose z
    rw [dist_eq_norm] at hz
    exact (norm_sub_rev _ _).trans_lt hz
  have hcap : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < widthCap :=
    (eventually_lt_nhds hwidthCap).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε < widthCap ∧ ∀ i : Fin 6, ∀ z : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ i.val (G ε) z - iteratedFDeriv ℝ i.val g z‖ < δ := by
    filter_upwards [self_mem_nhdsWithin, hcap, hs] with ε hε hc he
    exact ⟨hε, hc, he⟩
  obtain ⟨ε, hε, hc, he⟩ := hall.exists
  have hGe : ContDiff ℝ ∞ (G ε) := hreg ε hε
  refine ⟨ε, hε, hc, hGe.comp e.contDiff, ?_⟩
  intro p i hi
  have herr : (G ε ∘ e) - f0 = (G ε - g) ∘ e := by
    funext z
    simp only [Pi.sub_apply, Function.comp_apply, g, e.symm_apply_apply]
  rw [herr]
  have hcoord := collarHopf_ambient_coordinate_jet_bound C (G ε - g) (hGe.sub hg) p i
  have heu : ‖iteratedFDeriv ℝ i (G ε - g) (e p)‖ ≤ δ := by
    rw [iteratedFDeriv_sub_apply (hGe.contDiffAt.of_le (by simp))
      (hg.contDiffAt.of_le (by simp))]
    exact (he (⟨i, by omega⟩ : Fin 6) (e p)).le
  calc
    _ ≤ ‖iteratedFDeriv ℝ i (G ε - g) (e p)‖ * ‖e.toContinuousLinearMap‖ ^ i := hcoord
    _ ≤ δ * S := mul_le_mul heu (hpow i hi) (pow_nonneg (norm_nonneg _) _) hδ.le
    _ = τ := div_mul_cancel₀ _ hS.ne'

end GlobalEmbedding.Paper
