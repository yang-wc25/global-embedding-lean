import GlobalEmbedding.Paper.CollarAmbientHopfSourceCoefficients
import GlobalEmbedding.Paper.CollarAffineJetBound
import GlobalEmbedding.Paper.FreeHopfOrbitLift
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual ambient-to-orbit jet bounds on the original compact Hopf product

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-ambient-orbit-jet-bound`; exclusive AS2b owner W2.
The full actual action jets are bounded on compact original zero-time data.
Reuse Mathlib's full composition estimate, retaining all nonlinear action terms.
-/

noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual ambient jets on the original compact inclusion control every genuine
Euclidean multi-orbit jet, uniformly in all original points and ALL real times.
The constant is constructed only from the actual action, compact product and
fixed finite order, BEFORE the observable or approximation is chosen.

Proof: bound the full joint action jets on compact (inclusion x,0). The accepted
affine bound controls its time restrictions with the genuine product injection.
Apply Mathlib's full iterated-composition estimate. Original action addition and
the actual translation identity for jets move every time to zero at another
original compact point. No desired action-jet or orbit-jet bound is assumed.
Source: the actual ambient C5 approximation in prop:collar, lines520–526. -/
theorem collarHopf_ambient_orbit_jet_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ R : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ R →
      ∀ ε : ℝ, 0 ≤ ε →
        (∀ x : FreeHopfProduct C, ∀ i ≤ k,
          ‖iteratedFDeriv ℝ i R (freeHopfAmbientInclusion C x)‖ ≤ ε) →
        ∀ x : FreeHopfProduct C, ∀ y : EuclideanSpace ℝ (Fin a), ∀ n ≤ k,
          ‖iteratedFDeriv ℝ n
            (fun t : EuclideanSpace ℝ (Fin a) ↦
              R (freeHopfAmbientInclusion C (freeHopfOrbitLift C x t))) y‖ ≤ B * ε := by
  let E := FreeHopfAmbientSpace C
  let Y := EuclideanSpace ℝ (Fin a)
  let J : E × Y → E := fun q ↦ collarAmbientHopfAction C (fun i ↦ q.2 i) q.1
  have htime : ContDiff ℝ ∞ (fun q : E × Y ↦ ((fun i : Fin a ↦ q.2 i), q.1)) :=
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a ↦ ℝ)).contDiff.comp
      contDiff_snd).prodMk contDiff_fst)
  have hact : ContDiff ℝ ∞ (fun q : (Fin a → ℝ) × E ↦
      collarAmbientHopfAction C q.1 q.2) :=
    (collarAmbientHopfAction_contDiff C).of_le (by simp)
  have hJ : ContDiff ℝ ∞ J := by
    simpa only [J, Function.comp_def] using hact.comp htime
  let c : FreeHopfProduct C → E × Y := fun x ↦ (freeHopfAmbientInclusion C x, 0)
  have hc : Continuous c :=
    (freeHopfAmbientInclusion_contMDiff C).continuous.prodMk continuous_const
  let S : FreeHopfProduct C → ℝ := fun x ↦
    ∑ i : Fin (k + 1), ‖iteratedFDeriv ℝ i.val J (c x)‖
  have hS : Continuous S := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((hJ.continuous_iteratedFDeriv (m := i.val) (by simp)).comp hc).norm
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (FreeHopfProduct C)))
    |>.exists_bound_of_continuousOn hS.continuousOn
  let actionBound := max 1 M
  have hD : 1 ≤ actionBound := le_max_left _ _
  have hD0 : 0 ≤ actionBound := zero_le_one.trans hD
  have hjet (x : FreeHopfProduct C) (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i J (c x)‖ ≤ actionBound := by
    have hs : ‖iteratedFDeriv ℝ i J (c x)‖ ≤ S x :=
      Finset.single_le_sum
        (f := fun j : Fin (k + 1) ↦ ‖iteratedFDeriv ℝ j.val J (c x)‖)
        (fun j _ ↦ norm_nonneg _) (Finset.mem_univ
          (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (k + 1)))
    exact hs.trans ((le_abs_self (S x)).trans ((hM x (mem_univ x)).trans (le_max_right _ _)))
  let L : Y →L[ℝ] E × Y := ContinuousLinearMap.inr ℝ E Y
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [L]
  let O : FreeHopfProduct C → Y → E := fun x y ↦
    freeHopfAmbientInclusion C (freeHopfOrbitLift C x y)
  have hOeq (x : FreeHopfProduct C) : O x = fun y ↦ J (c x + L y) := by
    funext y
    dsimp only [O, J, c, L]
    simp only [ContinuousLinearMap.inr_apply, Prod.fst_add, Prod.snd_add, add_zero, zero_add]
    exact (collarAmbientHopfAction_inclusion C (fun i ↦ y i) x).symm
  have hO (x : FreeHopfProduct C) : ContDiff ℝ ∞ (O x) := by
    rw [hOeq]
    exact hJ.comp (contDiff_const.add L.contDiff)
  have hOzero (x : FreeHopfProduct C) : O x 0 = freeHopfAmbientInclusion C x := by
    simp only [O, freeHopfOrbitLift_zero]
  have hOjet (x : FreeHopfProduct C) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (O x) 0‖ ≤ actionBound ^ i := by
    have hb := collar_affine_jet_bound J (c x) L (0 : Y) i
      (by simpa only [map_zero, add_zero] using (hJ.of_le (by simp)).contDiffAt)
    have hb' : ‖iteratedFDeriv ℝ i (O x) 0‖ ≤
        ‖iteratedFDeriv ℝ i J (c x)‖ * ‖L‖ ^ i := by
      simpa only [← hOeq x, map_zero, add_zero] using hb
    calc
      _ ≤ ‖iteratedFDeriv ℝ i J (c x)‖ * ‖L‖ ^ i := hb'
      _ ≤ actionBound * 1 := mul_le_mul (hjet x i hi) (pow_le_one₀ (norm_nonneg _) hL)
        (pow_nonneg (norm_nonneg _) _) hD0
      _ = actionBound := mul_one _
      _ ≤ actionBound ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hD hi1
  let B := 1 + ∑ i : Fin (k + 1), (i.val.factorial : ℝ) * actionBound ^ i.val
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro R hR ε hε houter x y n hn
  have hzero (z : FreeHopfProduct C) :
      ‖iteratedFDeriv ℝ n (fun t : Y ↦ R (O z t)) 0‖ ≤ B * ε := by
    have hcR : ∀ i ≤ n, ‖iteratedFDeriv ℝ i R (O z 0)‖ ≤ ε := by
      intro i hi
      rw [hOzero]
      exact houter z i (hi.trans hn)
    have hcomp := norm_iteratedFDeriv_comp_le hR (hO z) (show (n : ℕ∞ω) ≤ ∞ by simp)
      (0 : Y) hcR (fun i hi1 hi ↦ hOjet z i hi1 (hi.trans hn))
    have hsum : (n.factorial : ℝ) * actionBound ^ n ≤ B := by
      have hs : (n.factorial : ℝ) * actionBound ^ n ≤
          ∑ i : Fin (k + 1), (i.val.factorial : ℝ) * actionBound ^ i.val :=
        Finset.single_le_sum
          (f := fun i : Fin (k + 1) ↦ (i.val.factorial : ℝ) * actionBound ^ i.val)
          (fun i _ ↦ by positivity)
          (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (k + 1)))
      exact hs.trans (le_add_of_nonneg_left zero_le_one)
    calc
      _ ≤ (n.factorial : ℝ) * ε * actionBound ^ n := hcomp
      _ = ((n.factorial : ℝ) * actionBound ^ n) * ε := by ring
      _ ≤ B * ε := mul_le_mul_of_nonneg_right hsum hε
  have hshift : (fun t : Y ↦ R (O (freeHopfOrbitLift C x y) t)) =
      (fun t : Y ↦ R (O x (t + y))) := by
    funext t
    congr 1
    change freeHopfAmbientInclusion C
        (freeHopfRealAction C (fun i ↦ t i) (freeHopfRealAction C (fun i ↦ y i) x)) =
      freeHopfAmbientInclusion C (freeHopfRealAction C (fun i ↦ (t + y) i) x)
    rw [← freeHopfRealAction_add]
    rfl
  have hh := hzero (freeHopfOrbitLift C x y)
  rw [hshift] at hh
  rw [iteratedFDeriv_comp_add_right (f := fun t : Y ↦ R (O x t))] at hh
  simpa only [zero_add, O] using hh

end GlobalEmbedding.Paper
