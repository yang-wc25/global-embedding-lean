import GlobalEmbedding.Paper.FreeGramRightInverse
import GlobalEmbedding.Paper.FreeNormalizedScaleAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Actual buffered Gram reconstruction and two-patch gluing

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–489.
The original whole-parent column and pivot instantiation is a separate obligation.
-/

noncomputable section
open scoped ContDiff Manifold Topology
open Set Function

namespace GlobalEmbedding.Paper

/-- The actual fixed scalar cutoff, with both support boundaries strictly inside the rank patches.
It is a smooth even function of curvature; no absolute-value differentiation is used. -/
def freeInversePatchBump (d : ℝ) (hd : 0 < d) : ContDiffBump (0 : ℝ) where
  rIn := d / 2
  rOut := 3 * d / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Literal near-patch weight of the same curvature field. -/
def freeInverseNearWeight {M : Type*} (κ : M → ℝ) (d : ℝ) (hd : 0 < d) : M → ℝ :=
  fun x ↦ freeInversePatchBump d hd (κ x)

theorem freeInverseNearWeight_one {M : Type*} (κ : M → ℝ) (d : ℝ) (hd : 0 < d)
    (x : M) (hx : |κ x| ≤ d / 2) : freeInverseNearWeight κ d hd x = 1 := by
  apply (freeInversePatchBump d hd).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, freeInversePatchBump] using hx

theorem freeInverseNearWeight_zero {M : Type*} (κ : M → ℝ) (d : ℝ) (hd : 0 < d)
    (x : M) (hx : 3 * d / 4 ≤ |κ x|) : freeInverseNearWeight κ d hd x = 0 := by
  apply (freeInversePatchBump d hd).zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, freeInversePatchBump] using hx

variable {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual near weight is native smooth on the whole parameter manifold. -/
theorem freeInverseNearWeight_contMDiff (κ : M → ℝ)
    (hκ : ContMDiff I 𝓘(ℝ, ℝ) ∞ κ) (d : ℝ) (hd : 0 < d) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (freeInverseNearWeight κ d hd) :=
  (freeInversePatchBump d hd).contDiff.contMDiff.comp hκ

/-- The closed support of the actual near weight lies strictly inside the true near rank patch. -/
theorem freeInverseNearWeight_tsupport (κ : M → ℝ) (hκ : Continuous κ)
    (d : ℝ) (hd : 0 < d) :
    tsupport (freeInverseNearWeight κ d hd) ⊆ {x | |κ x| < d} := by
  have hs : tsupport (freeInverseNearWeight κ d hd) ⊆ {x | |κ x| ≤ 3 * d / 4} := by
    apply closure_minimal _ (isClosed_le hκ.abs continuous_const)
    intro x hx
    by_contra hn
    exact hx (freeInverseNearWeight_zero κ d hd x (le_of_not_ge hn))
  intro x hx
  have hx' : |κ x| ≤ 3 * d / 4 := hs hx
  change |κ x| < d
  linarith

/-- The closed support of the complementary weight stays inside the true far rank patch. -/
theorem freeInverseFarWeight_tsupport (κ : M → ℝ) (hκ : Continuous κ)
    (d : ℝ) (hd : 0 < d) :
    tsupport (fun x ↦ 1 - freeInverseNearWeight κ d hd x) ⊆ {x | d / 3 < |κ x|} := by
  have hs : tsupport (fun x ↦ 1 - freeInverseNearWeight κ d hd x) ⊆
      {x | d / 2 ≤ |κ x|} := by
    apply closure_minimal _ (isClosed_le continuous_const hκ.abs)
    intro x hx
    by_contra hn
    have hx' : |κ x| ≤ d / 2 := (lt_of_not_ge hn).le
    exact hx (by
      change 1 - freeInverseNearWeight κ d hd x = 0
      rw [freeInverseNearWeight_one κ d hd x hx', sub_self])
  intro x hx
  have hx' : d / 2 ≤ |κ x| := hs hx
  change d / 3 < |κ x|
  linarith

/-- A genuine support buffer makes the weighted local operator field globally native smooth,
even if its total formula is nonsmooth outside the open patch where it is actually invertible. -/
theorem free_weighted_patch_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (U : Set M) (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (B : M → F) (hB : ContMDiffOn I 𝓘(ℝ, F) ∞ B U) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun x ↦ χ x • B x) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxu : x ∈ U := hs (tsupport_smul_subset_left χ B hx)
  exact hχ.contMDiffAt.smul (hB.contMDiffAt (hU.mem_nhds hxu))

section GramPatches

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The true Gram reconstruction gives a native smooth normalized inverse on its injective patch.
The total Gram formula outside that patch is irrelevant to the later buffered extension. -/
theorem free_gram_patch_contMDiffOn (U : Set M)
    (J : V →L[ℝ] V) (prj : M → E →L[ℝ] E) (B : M → V →L[ℝ] E) (ε : M → ℝ)
    (hprj : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ prj U)
    (hB : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ B U)
    (hinj : ∀ x ∈ U, Function.Injective (B x))
    (hε : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ε U) :
    ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞
      (fun x ↦ freeNormalizedPairingInverse (prj x) (freeGramRightInverse (B x)) J (ε x)) U :=
  hprj.clm_comp ((freeGramRightInverse_contMDiffOn B hB hinj).clm_comp
    ((freeInverseScale_contDiff J).contMDiff.comp_contMDiffOn hε))

/-- The literal two-patch normalized inverse, formed from the actual Gram formulas.
The far patch has no ambient projection, and the two masks are allowed to be different. -/
def freeTwoPatchNormalizedInverse (κ : M → ℝ) (d : ℝ) (hd : 0 < d)
    (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (ε : M → ℝ) : M → V →L[ℝ] E :=
  fun x ↦ freeInverseNearWeight κ d hd x •
      freeNormalizedPairingInverse (prj x) (freeGramRightInverse (Bn x)) Jn (ε x) +
    (1 - freeInverseNearWeight κ d hd x) •
      freeNormalizedPairingInverse (ContinuousLinearMap.id ℝ E)
        (freeGramRightInverse (Bf x)) Jf (ε x)

/-- The actual fixed buffered weights make the two genuine Gram formulas native smooth globally,
using injectivity only on the near and far patches. No smoothness outside a patch is assumed. -/
theorem freeTwoPatchNormalizedInverse_contMDiff
    (κ : M → ℝ) (hκ : ContMDiff I 𝓘(ℝ, ℝ) ∞ κ) (d : ℝ) (hd : 0 < d)
    (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (ε : M → ℝ)
    (hprj : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ prj)
    (hBn : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bn {x | |κ x| < d})
    (hBf : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bf {x | d / 3 < |κ x|})
    (hin : ∀ x, |κ x| < d → Function.Injective (Bn x))
    (hif : ∀ x, d / 3 < |κ x| → Function.Injective (Bf x))
    (hε : ContMDiff I 𝓘(ℝ, ℝ) ∞ ε) :
    ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞
      (freeTwoPatchNormalizedInverse κ d hd prj Bn Bf Jn Jf ε) := by
  have hχ := freeInverseNearWeight_contMDiff κ hκ d hd
  have hnear := free_gram_patch_contMDiffOn {x | |κ x| < d} Jn prj Bn ε
    hprj.contMDiffOn hBn hin hε.contMDiffOn
  have hfar := free_gram_patch_contMDiffOn {x | d / 3 < |κ x|} Jf
    (fun _ ↦ ContinuousLinearMap.id ℝ E) Bf ε contMDiff_const.contMDiffOn hBf hif
    hε.contMDiffOn
  exact (free_weighted_patch_contMDiff _ hχ _
    (isOpen_lt hκ.continuous.abs continuous_const)
    (freeInverseNearWeight_tsupport κ hκ.continuous d hd) _ hnear).add
    (free_weighted_patch_contMDiff _ (contMDiff_const.sub hχ) _
      (isOpen_lt continuous_const hκ.continuous.abs)
      (freeInverseFarWeight_tsupport κ hκ.continuous d hd) _ hfar)

/-- The true two-patch reconstruction satisfies the scaled full-data identity everywhere.
Its two local identities follow from the actual normalized-column relations and Gram injectivity;
the actual cutoff support discharges exactly the patch membership needed for each term. -/
theorem freeTwoPatchNormalizedInverse_scaled_identity
    (κ : M → ℝ) (hκ : Continuous κ) (d : ℝ) (hd : 0 < d)
    (T : M → E →L[ℝ] V) (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (hJn : Jn.comp Jn = Jn) (hJf : Jf.comp Jf = Jf)
    (ε : M → ℝ)
    (hin : ∀ x, |κ x| < d → Function.Injective (Bn x))
    (hif : ∀ x, d / 3 < |κ x| → Function.Injective (Bf x))
    (hTn : ∀ x, |κ x| < d →
      (T x).comp (prj x) = (freeColumnScale Jn (ε x)).comp (Bn x).adjoint)
    (hTf : ∀ x, d / 3 < |κ x| →
      T x = (freeColumnScale Jf (ε x)).comp (Bf x).adjoint) (x : M) :
    (T x).comp (freeTwoPatchNormalizedInverse κ d hd prj Bn Bf Jn Jf ε x) =
      ε x • ContinuousLinearMap.id ℝ V := by
  let χ := freeInverseNearWeight κ d hd
  have hn : (T x).comp (χ x •
      freeNormalizedPairingInverse (prj x) (freeGramRightInverse (Bn x)) Jn (ε x)) =
      χ x • (ε x • ContinuousLinearMap.id ℝ V) := by
    rw [ContinuousLinearMap.comp_smul]
    by_cases hx : χ x = 0
    · simp [hx]
    have hpatch : |κ x| < d :=
      freeInverseNearWeight_tsupport κ hκ d hd (subset_tsupport χ hx)
    rw [free_normalized_pairing_identity Jn hJn (ε x) (T x) (prj x) (Bn x).adjoint
      (freeGramRightInverse (Bn x)) (hTn x hpatch)
      (freeGramRightInverse_spec (Bn x) (hin x hpatch))]
  have hf : (T x).comp ((1 - χ x) •
      freeNormalizedPairingInverse (ContinuousLinearMap.id ℝ E)
        (freeGramRightInverse (Bf x)) Jf (ε x)) =
      (1 - χ x) • (ε x • ContinuousLinearMap.id ℝ V) := by
    rw [ContinuousLinearMap.comp_smul]
    by_cases hx : 1 - χ x = 0
    · simp [hx]
    have hpatch : d / 3 < |κ x| :=
      freeInverseFarWeight_tsupport κ hκ d hd
        (subset_tsupport (fun y ↦ 1 - χ y) hx)
    rw [free_normalized_pairing_identity Jf hJf (ε x) (T x)
      (ContinuousLinearMap.id ℝ E) (Bf x).adjoint (freeGramRightInverse (Bf x))
      (by simpa only [ContinuousLinearMap.comp_id] using hTf x hpatch)
      (freeGramRightInverse_spec (Bf x) (hif x hpatch))]
  change (T x).comp (χ x • _ + (1 - χ x) • _) = _
  rw [ContinuousLinearMap.comp_add, hn, hf]
  module

end GramPatches

#print axioms freeInverseNearWeight_tsupport
#print axioms freeInverseFarWeight_tsupport
#print axioms free_weighted_patch_contMDiff
#print axioms freeTwoPatchNormalizedInverse_contMDiff
#print axioms freeTwoPatchNormalizedInverse_scaled_identity

end GlobalEmbedding.Paper
