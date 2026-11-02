import GlobalEmbedding.Paper.CollarHopfOrbitGramJetBound
import GlobalEmbedding.Paper.CollarHopfGramCofactorCoordinates
import GlobalEmbedding.Paper.FreeHopfOrbitSourceData
import GlobalEmbedding.Paper.CollarSmoothHolderSlice
import GlobalEmbedding.Paper.BalancedHolderMultiplicationBounded

/-!
# Uniform original little multiplier bounds for actual ambient Hopf coefficients

Source: `main.tex`, prop:collar, lines522–534.
DAG: `collar-hopf-ambient-little-multiplier-bound`; sole AS2b owner W2.
Actual cofactor permutation and HS flattening retain their genuine CLM norms.
Original little membership/norm and multiplication are reused, not reproved.
-/

noncomputable section
open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A fixed actual smooth ambient extension with free native restriction gives
a fixed C5 neighborhood and a common bound in the ORIGINAL little coefficient
and multiplier norms, BEFORE choosing any approximating F.

The coefficient lift is EXACTLY the actual ordinary-transpose matrix formula
in the existing cofactor order. The multiplier bound holds for EVERY multiplier
with the genuine existing HS pointwise formula, including the accepted69 one.

Proof: the accepted C5 Gram estimate and exact cofactor matrix identity identify
the actual coefficient as a fixed continuous linear coordinate map of the same
native inverse. Its actual norm bounds all coefficient jets through three.
Original action periodicity and accepted smooth-to-little Holder slice construct
the actual coefficient. Accepted bounded multiplication and function injectivity
identify every same-formula multiplier with the canonical one and bound its norm.
No generic Gram, inverse, Holder or multiplication estimate is reproved.
Source: quantitative analytic correction in prop:collar, lines522–534. -/
theorem collarHopf_fixed_ambient_c5_little_multiplier_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hf0 : ContDiff ℝ ∞ f0)
    (hfree : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (f0 ∘ freeHopfAmbientInclusion C) x)) :
    let M := freeSymmetricColumnCount a + a
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      ∀ F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ F →
        (∀ x : FreeHopfProduct C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i (F - f0) (freeHopfAmbientInclusion C x)‖ ≤ η) →
        ∀ x : FreeHopfProduct C,
        ∃ coeff : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ),
          (∀ y : EuclideanSpace ℝ (Fin a), ∀ q : Fin (N * M),
            let T := collarAmbientHopfPairingMatrix C F
              (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
            coeff.val.toFun y q =
              (T.transpose * (T * T.transpose)⁻¹)
                (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) ∧
          ‖coeff‖ ≤ K ∧
          ∀ mult : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ) →L[ℝ]
              LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
                LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
            (∀ A u y, (mult A u).val.toFun y =
              hilbertSchmidtCoordinateEvaluation M N (A.val.toFun y) (u.val.toFun y)) →
            ‖mult coeff‖ ≤ K := by
  let M := freeSymmetricColumnCount a + a
  let E := EuclideanSpace ℝ (BalancedPairingIndex a)
  let V := EuclideanSpace ℝ (Fin M)
  let W := EuclideanSpace ℝ (Fin N)
  let e : E ≃ₗᵢ[ℝ] V :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a)
  let b : (E →L[ℝ] W) →L[ℝ] EuclideanSpace ℝ (Fin (N * M)) :=
    (((e.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ W)).trans
      (hilbertSchmidtCoordinateEquiv M N).symm.toContinuousLinearEquiv).toContinuousLinearMap)
  obtain ⟨η, J, hη, hJ, hgram⟩ := collarHopf_fixed_ambient_c5_gram_bound C f0 hf0 hfree
  let Cjet := ‖b‖ * J
  have hCjet : 0 ≤ Cjet := mul_nonneg (norm_nonneg b) hJ.le
  let Tori := PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))
  have hcompact : IsCompact (univ : Set Tori) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) → Tori) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨diameterBound, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  have hdiameter : 0 ≤ diameterBound := by
    simpa only [dist_self] using hD (x := (0 : Tori)) (mem_univ _) (y := (0 : Tori)) (mem_univ _)
  let Hbound := 3 * Cjet + Cjet * diameterBound ^ (1 - (1 / 2 : ℝ))
  have hHbound : 0 ≤ Hbound := by dsimp only [Hbound]; positivity
  obtain ⟨_, _, mult0, hmult0, hmultBound⟩ :=
    balanced_holder_multiplication_bounded (a := a) (M := M) (N := N) (k := 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨Cmult, hCmult, hMbound⟩ := hmultBound
  let K := 1 + Hbound + Cmult * Hbound
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨η, K, hη, hK, ?_⟩
  intro F hF hclose x
  obtain ⟨hR, _, hRb⟩ := hgram F hF hclose x
  let R : EuclideanSpace ℝ (Fin a) → E →L[ℝ] W := fun t ↦ freeGramRightInverse
    (freeColumnOperator (freeFlowColumns (freeHopfProductFlow C)
      (F ∘ freeHopfAmbientInclusion C) (freeHopfOrbitLift C x t)))
  let g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin (N * M)) := fun t ↦ b (R t)
  have hg : ContDiff ℝ ∞ g := b.contDiff.comp hR
  have hgb (n : ℕ) (hn : n ≤ 3) (y : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ n g y‖ ≤ Cjet := by
    have he := b.norm_iteratedFDeriv_comp_left (x := y) hR.contDiffAt
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    exact he.trans (mul_le_mul_of_nonneg_left (hRb n hn y) (norm_nonneg _))
  have hperiod (y : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
      g (y + toLp 2 (fun i ↦ (m i : ℝ))) = g y := by
    change b (freeGramRightInverse (freeColumnOperator
      (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C)
        (freeHopfRealAction C (fun i ↦ (y + toLp 2 (fun j ↦ (m j : ℝ))) i) x)))) = _
    rw [freeHopfRealAction_integer_periodic]
    rfl
  have hflat (z : FreeHopfProduct C) :
      b (freeGramRightInverse (freeColumnOperator
        (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) z))) =
      toLp 2 (fun q : Fin (N * M) ↦
        let T := collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C z)
        (T.transpose * (T * T.transpose)⁻¹)
          (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) := by
    change (hilbertSchmidtCoordinateEquiv M N).symm
      ((freeGramRightInverse (freeColumnOperator
        (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) z))).comp
          e.symm.toContinuousLinearMap) = _
    rw [← collarHopf_gram_cofactor_coordinates C F z]
    simp only [hilbertSchmidtCoordinateEquiv, LinearEquiv.trans_symm,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨coeff, heq, hnorm⟩ := collar_smooth_holder_slice (k := 2) (α := (1 / 2 : ℝ))
    g hg hperiod (fun _ ↦ Cjet) (fun n hn y _ ↦ hgb n hn y) (by norm_num) diameterBound
    (fun y z ↦ hD (mem_univ _) (mem_univ _))
  have hcoeff : ‖coeff‖ ≤ Hbound := by
    simpa [Hbound] using hnorm
  refine ⟨coeff, ?_, hcoeff.trans ?_, ?_⟩
  · intro y q
    rw [heq]
    change g y q = _
    rw [collarAmbientHopfAction_inclusion]
    exact congrArg (fun w : EuclideanSpace ℝ (Fin (N * M)) ↦ w q)
      (hflat (freeHopfOrbitLift C x y))
  · dsimp only [K]
    linarith [mul_nonneg hCmult hHbound]
  · intro mult hmult
    have heMult : mult = mult0 := by
      apply ContinuousLinearMap.ext
      intro A
      apply ContinuousLinearMap.ext
      intro u
      apply Subtype.ext
      apply periodicCAlpha_toFun_injective
      funext y
      rw [hmult, hmult0]
    rw [heMult]
    have hOp : ‖mult0 coeff‖ ≤ Cmult * ‖coeff‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCmult (norm_nonneg coeff))
      intro u
      exact hMbound coeff u
    have he := hOp.trans (mul_le_mul_of_nonneg_left hcoeff hCmult)
    exact he.trans (by dsimp only [K]; linarith)

end GlobalEmbedding.Paper
