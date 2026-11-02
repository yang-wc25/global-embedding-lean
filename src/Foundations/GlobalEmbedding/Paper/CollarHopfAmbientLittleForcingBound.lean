import GlobalEmbedding.Paper.CollarHopfAmbientOrbitJetBound
import GlobalEmbedding.Paper.CollarHopfColumnSubtraction
import GlobalEmbedding.Paper.CollarAmbientHopfSourceCoefficients
import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.FreeHopfOrbitSourceData
import GlobalEmbedding.Paper.FrameGramCjEstimates
import GlobalEmbedding.Paper.CollarSmoothHolderSlice

/-!
# The actual OLD Gram forcing tends to zero in the ORIGINAL little norm

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-ambient-little-forcing-bound`; sole AS2b owner W2.
The actual first frame is the genuine Fréchet derivative of the orbit observable.
Reuse the accepted full orbit/Gram/Holder estimates and native subtraction body.
The raw datum is (0,Gamma-I), with NO half; the accepted69 endpoint inserts half.
-/

noncomputable section
open Set Function WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A FIXED smooth compact ambient extension whose original native first Gram
is identity gives a common linear ORIGINAL little-norm forcing bound BEFORE F.

The returned actual lift is the raw (0,OLDGamma(F)-I), in the SAME cofactor
order as the actual T_F matrix, with no half inserted. Genuine ambient C5 error
epsilon<=1 bounds its original little c^(2,1/2) norm by K*epsilon, so it tends
to zero with the actual approximation error, with no desired forcing premise.

Proof: Mathlib compact-support jet bounds and the accepted orbit composition
bound control the genuine first frame fderiv of the orbit observable. Its error
is the derivative of the actual error observable by the accepted native first
lift and public reused subtraction identity on the actual Euclidean basis.
The accepted Gram Cj comparison bounds Gram-error jets by O(epsilon). A fixed
actual cofactor-packing CLM and exact original identity Gram identify the OLD
forcing. Its actual norm and the accepted smooth Holder slice give the result.
No generic composition/Gram/Holder estimate is reproved.
Source: prop:collar, genuine approximation/small forcing, lines520–526. -/
theorem collarHopf_ambient_c5_little_forcing_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hf0 : ContDiff ℝ ∞ f0)
    (hcompact0 : HasCompactSupport f0)
    (hmetric0 : ∀ z : FreeHopfProduct C,
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (f0 ∘ freeHopfAmbientInclusion C) z) = 1) :
    let M := freeSymmetricColumnCount a + a
    ∃ K : ℝ, 0 < K ∧
      ∀ F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ F →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        (∀ z : FreeHopfProduct C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i (F - f0) (freeHopfAmbientInclusion C z)‖ ≤ ε) →
        ∀ x : FreeHopfProduct C,
        ∃ h : LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ),
          (∀ y : EuclideanSpace ℝ (Fin a), ∀ r : Fin M,
            h.val.toFun y r = match (freeCofactorColumnOrder a).symm r with
              | Sum.inl _ => 0
              | Sum.inr ij => collarAmbientHopfMetricDefect C F
                  (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
                    ij.val.1 ij.val.2) ∧
          ‖h‖ ≤ K * ε := by
  let M := freeSymmetricColumnCount a + a
  let Y := EuclideanSpace ℝ (Fin a)
  let W := EuclideanSpace ℝ (Fin N)
  let pack : (Y →L[ℝ] Y) →L[ℝ] EuclideanSpace ℝ (Fin M) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun r : Fin M ↦
        match (freeCofactorColumnOrder a).symm r with
        | Sum.inl _ => 0
        | Sum.inr ij => (EuclideanSpace.proj ij.val.1).comp
            (ContinuousLinearMap.apply ℝ Y (EuclideanSpace.single ij.val.2 1))))
  have hpack (H : Y →L[ℝ] Y) (r : Fin M) : pack H r =
      match (freeCofactorColumnOrder a).symm r with
      | Sum.inl _ => 0
      | Sum.inr ij => H (EuclideanSpace.single ij.val.2 1) ij.val.1 := by
    cases he : (freeCofactorColumnOrder a).symm r <;> simp [pack, he]
  obtain ⟨K0, hK0, hbasejet⟩ := hcompact0.exists_bound_iteratedFDeriv hf0 5
  obtain ⟨B, hB, hb⟩ := collarHopf_ambient_orbit_jet_bound (N := N) C 5
  let L := B * (K0 + 1)
  have hL : 0 ≤ L := mul_nonneg hB.le (by positivity)
  let Cjet := ‖pack‖ * (64 * L * B)
  have hCjet : 0 ≤ Cjet := mul_nonneg (norm_nonneg pack) (by positivity)
  let Tori := PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))
  have htorus : IsCompact (univ : Set Tori) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) → Tori) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨diameterBound, hdiameter⟩ := Metric.isBounded_iff.mp htorus.isBounded
  have hdiam0 : 0 ≤ diameterBound := by
    simpa only [dist_self] using
      hdiameter (x := (0 : Tori)) (mem_univ _) (y := (0 : Tori)) (mem_univ _)
  let K := 1 + (3 + diameterBound ^ (1 - (1 / 2 : ℝ))) * Cjet
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro F hF ε hε hε1 hclose x
  let U := F ∘ freeHopfAmbientInclusion C
  let U0 := f0 ∘ freeHopfAmbientInclusion C
  have hU := hF.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  have hU0 := hf0.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  let g := U ∘ freeHopfOrbitLift C x
  let g0 := U0 ∘ freeHopfOrbitLift C x
  let ge := (U - U0) ∘ freeHopfOrbitLift C x
  have hg : ContDiff ℝ ∞ g := (hU.comp (freeHopfOrbitLift_contMDiff C x)).contDiff
  have hg0 : ContDiff ℝ ∞ g0 := (hU0.comp (freeHopfOrbitLift_contMDiff C x)).contDiff
  let A : Y → Y →L[ℝ] W := fderiv ℝ g
  let A0 : Y → Y →L[ℝ] W := fderiv ℝ g0
  have hA : ContDiff ℝ ∞ A := hg.fderiv_right (by simp)
  have hA0 : ContDiff ℝ ∞ A0 := hg0.fderiv_right (by simp)
  have hfirst (P : FreeHopfProduct C → W)
      (hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, W) ∞ P) (y : Y) (i : Fin a) :
      fderiv ℝ (P ∘ freeHopfOrbitLift C x) y (EuclideanSpace.single i 1) =
        freeHopfDeriv C i P (freeHopfOrbitLift C x y) := by
    rw [← freeHopf_first_orbitLift C P hP x y i]
    exact freeHopfGenerator_mvfderiv C i P hP _
  have hAdiff : A - A0 = fderiv ℝ ge := by
    funext y
    have he : (A y - A0 y).toLinearMap = (fderiv ℝ ge y).toLinearMap := by
      apply (EuclideanSpace.basisFun (Fin a) ℝ).toBasis.ext
      intro i
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      change A y (EuclideanSpace.single i 1) - A0 y (EuclideanSpace.single i 1) =
        fderiv ℝ ge y (EuclideanSpace.single i 1)
      rw [hfirst U hU, hfirst U0 hU0, hfirst (U - U0) (hU.sub hU0)]
      exact (congrFun (freeHopfDeriv_sub C U U0 hU hU0 i) _).symm
    exact congrArg (fun L ↦ LinearMap.toContinuousLinearMap L) he
  have houter (z : FreeHopfProduct C) (i : ℕ) (hi : i ≤ 5) :
      ‖iteratedFDeriv ℝ i F (freeHopfAmbientInclusion C z)‖ ≤ K0 + 1 := by
    have he := hclose z i hi
    rw [iteratedFDeriv_sub_apply (hF.contDiffAt.of_le (by simp))
      (hf0.contDiffAt.of_le (by simp))] at he
    have hh := norm_le_norm_sub_add
      (iteratedFDeriv ℝ i F (freeHopfAmbientInclusion C z))
      (iteratedFDeriv ℝ i f0 (freeHopfAmbientInclusion C z))
    linarith [hbasejet i hi (freeHopfAmbientInclusion C z)]
  have hAb (n : ℕ) (hn : n ≤ 3) (y : Y) : ‖iteratedFDeriv ℝ n A y‖ ≤ L := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hb F hF (K0 + 1) (by positivity) houter x y (n + 1) (by omega)
  have hA0b (n : ℕ) (hn : n ≤ 3) (y : Y) : ‖iteratedFDeriv ℝ n A0 y‖ ≤ L := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hb f0 hf0 (K0 + 1) (by positivity)
      (fun z i hi ↦ (hbasejet i hi _).trans (le_add_of_nonneg_right zero_le_one))
      x y (n + 1) (by omega)
  have heAb (n : ℕ) (hn : n ≤ 3) (y : Y) : ‖iteratedFDeriv ℝ n (A - A0) y‖ ≤ B * ε := by
    rw [hAdiff, norm_iteratedFDeriv_fderiv]
    exact hb (F - f0) (hF.sub hf0) ε hε hclose x y (n + 1) (by omega)
  obtain ⟨_, _, hGG, hGG0, _, hdBdd, _, hGramDiff, _⟩ :=
    frame_gram_cj_estimates 3 univ isOpen_univ A A0 hA.contDiffOn hA0.contDiffOn
      L hL (fun n hn y _ ↦ hAb n hn y) (fun n hn y _ ↦ hA0b n hn y)
  have hdelta : finiteCjNorm 3 (A - A0) univ ≤ 4 * B * ε := by
    have he := (finiteCjNorm_specification 3 (A - A0) univ hdBdd).2.2.1
      (fun _ ↦ B * ε) (fun _ _ ↦ mul_nonneg hB.le hε) (fun n hn y _ ↦ heAb n hn y)
    simpa [mul_assoc] using he
  let G := fun y : Y ↦ (A y).adjoint.comp (A y)
  let G0 := fun y : Y ↦ (A0 y).adjoint.comp (A0 y)
  have hGdiff (n : ℕ) (hn : n ≤ 3) (y : Y) :
      ‖iteratedFDeriv ℝ n (G - G0) y‖ ≤ 64 * L * B * ε := by
    have he := hGramDiff n hn y (mem_univ y)
    have he' : ‖iteratedFDeriv ℝ n (G - G0) y‖ ≤ 16 * L * finiteCjNorm 3 (A - A0) univ := by
      simpa only [G, G0, show (2 : ℝ) * 2 ^ 3 = 16 by norm_num] using he
    calc
      _ ≤ 16 * L * finiteCjNorm 3 (A - A0) univ := he'
      _ ≤ 16 * L * (4 * B * ε) := mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = _ := by ring
  let forcing : Y → EuclideanSpace ℝ (Fin M) := fun y ↦ pack ((G - G0) y)
  have hf : ContDiff ℝ ∞ forcing := pack.contDiff.comp
    ((contDiffOn_univ.mp hGG).sub (contDiffOn_univ.mp hGG0))
  have hfb (n : ℕ) (hn : n ≤ 3) (y : Y) :
      ‖iteratedFDeriv ℝ n forcing y‖ ≤ Cjet * ε := by
    have he := pack.norm_iteratedFDeriv_comp_left (x := y)
      (((contDiffOn_univ.mp hGG).sub (contDiffOn_univ.mp hGG0)).contDiffAt)
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    exact (he.trans (mul_le_mul_of_nonneg_left (hGdiff n hn y) (norm_nonneg pack))).trans
      (by dsimp only [Cjet]; exact le_of_eq (by ring))
  have hentry (Q : Y →L[ℝ] W) (i j : Fin a) :
      (Q.adjoint.comp Q) (EuclideanSpace.single j 1) i =
        inner ℝ (Q (EuclideanSpace.single i 1)) (Q (EuclideanSpace.single j 1)) := by
    have he := EuclideanSpace.inner_single_left i (1 : ℝ)
      (Q.adjoint (Q (EuclideanSpace.single j 1)))
    simp only [map_one, one_mul] at he
    exact he.symm.trans
      (Q.adjoint_inner_right (EuclideanSpace.single i 1) (Q (EuclideanSpace.single j 1)))
  have hvalues (y : Y) (r : Fin M) : forcing y r =
      match (freeCofactorColumnOrder a).symm r with
      | Sum.inl _ => 0
      | Sum.inr ij => collarAmbientHopfMetricDefect C F
          (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
            ij.val.1 ij.val.2 := by
    dsimp only [forcing]
    rw [hpack]
    cases he : (freeCofactorColumnOrder a).symm r with
    | inl i => rfl
    | inr ij =>
      change (G y (EuclideanSpace.single ij.val.2 1)) ij.val.1 -
        (G0 y (EuclideanSpace.single ij.val.2 1)) ij.val.1 = _
      rw [hentry, hentry, hfirst U hU, hfirst U hU, hfirst U0 hU0, hfirst U0 hU0,
        collarAmbientHopfAction_inclusion, collarAmbientHopfMetricDefect_inclusion]
      have h0 := congrArg (fun H : Matrix (Fin a) (Fin a) ℝ ↦ H ij.val.1 ij.val.2)
        (hmetric0 (freeHopfOrbitLift C x y))
      simp only [Matrix.gram_apply] at h0
      rw [h0]
      rfl
  have hperiod (y : Y) (m : Fin a → ℤ) :
      forcing (y + toLp 2 (fun i ↦ (m i : ℝ))) = forcing y := by
    apply PiLp.ext
    intro r
    rw [hvalues, hvalues]
    cases he : (freeCofactorColumnOrder a).symm r with
    | inl i => rfl
    | inr ij =>
      change collarAmbientHopfMetricDefect C F
        (collarAmbientHopfAction C (fun i ↦ y i + (m i : ℝ)) (freeHopfAmbientInclusion C x))
          ij.val.1 ij.val.2 =
        collarAmbientHopfMetricDefect C F
          (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
            ij.val.1 ij.val.2
      rw [collarAmbientHopfAction_integer_periodic]
  obtain ⟨h, heq, hnorm⟩ := collar_smooth_holder_slice (k := 2) (α := (1 / 2 : ℝ))
    forcing hf hperiod (fun _ ↦ Cjet * ε) (fun n hn y _ ↦ hfb n hn y) (by norm_num)
    diameterBound (fun y z ↦ hdiameter (mem_univ _) (mem_univ _))
  refine ⟨h, ?_, ?_⟩
  · intro y r
    rw [heq]
    exact hvalues y r
  · have he : ‖h‖ ≤ 3 * (Cjet * ε) + Cjet * ε * diameterBound ^ (1 - (1 / 2 : ℝ)) := by
      simpa using hnorm
    dsimp only [K]
    nlinarith

end GlobalEmbedding.Paper
