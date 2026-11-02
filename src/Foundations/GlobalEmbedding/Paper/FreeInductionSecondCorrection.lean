import GlobalEmbedding.Paper.FreeHopfProductGenerators
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute
import GlobalEmbedding.Paper.FreeInductionEuclideanBlocks
import GlobalEmbedding.Paper.FreeOldPairingLift
import GlobalEmbedding.Paper.FreeSecondCancellationRows

/-!
# Constructing W and cancelling the entire genuine quadratic metric term

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 470–475.
DAG node: `free-induction-second-correction`. All source flows and target blocks are shared.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

private theorem free_basic_pairing_derivative
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace Q] [ChartedSpace P Q]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) Q) (a W : Q → V) (w : Q → ℝ)
    (hW : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V) ∞ W)
    (hw : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ w)
    (ha : ∀ t x, a (R.flow t x) = a x)
    (hpair : ∀ x, inner ℝ (a x) (W x) = w x) (x : Q) :
    inner ℝ (a x) (orbitDeriv R.flow W x) = orbitDeriv R.flow w x := by
  have dW : HasDerivAt (fun t : ℝ ↦ W (R.flow t x)) (orbitDeriv R.flow W x) 0 := by
    simpa only [R.flow_zero] using hasDerivAt_orbit R.flow R.smooth R.flow_add W hW 0 x
  have dw : HasDerivAt (fun t : ℝ ↦ w (R.flow t x)) (orbitDeriv R.flow w x) 0 := by
    simpa only [R.flow_zero] using hasDerivAt_orbit R.flow R.smooth R.flow_add w hw 0 x
  have hi := (innerSL ℝ (a x)).hasFDerivAt.comp_hasDerivAt 0 dW
  have heq : (fun t : ℝ ↦ inner ℝ (a x) (W (R.flow t x))) =
      fun t ↦ w (R.flow t x) := by
    funext t
    rw [← ha t x, hpair]
  change HasDerivAt (fun t : ℝ ↦ inner ℝ (a x) (W (R.flow t x))) _ 0 at hi
  rw [heq] at hi
  exact hi.unique dw

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

private theorem free_step_directional {N : ℕ}
    (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (i : Fin (m + 1)) (x : FreeHopfProduct C) :
    balancedDirectionalDerivative F (freeHopfGeneratorSection C i) x =
      freeHopfDeriv C i F x := by
  change mvfderiv (freeHopfModel C) F x (freeHopfGenerator C i x) = _
  exact freeHopfGenerator_mvfderiv C i F hF x

private theorem free_step_scalar_directional (w : FreeHopfProduct C → ℝ)
    (hw : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ w)
    (i : Fin (m + 1)) (x : FreeHopfProduct C) :
    balancedScalarDirectionalDerivative w (freeHopfGeneratorSection C i) x =
      freeHopfDeriv C i w x := by
  exact freeHopfGenerator_mvfderiv C i w hw x

private theorem free_step_block_directional
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (p : FreeHopfProduct C → Planar)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hp : ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ p)
    (i : Fin (m + 1)) (x : FreeHopfProduct C) :
    balancedDirectionalDerivative (fun y ↦ freeInductionBlock K m (H y) (p y) 0)
        (freeHopfGeneratorSection C i) x =
      freeInductionBlock K m (freeHopfDeriv C i H x) (freeHopfDeriv C i p x) 0 := by
  rw [free_step_directional C _
    (freeInductionBlock_contMDiff K m H p (fun _ ↦ 0) hH hp contMDiff_const)]
  unfold freeHopfDeriv
  have hd := freeInductionBlock_orbitDeriv (freeHopfProductSmoothFlow C i) K m H p
    (fun _ ↦ 0) hH hp contMDiff_const x
  simpa only [freeHopfProductSmoothFlow, orbitDeriv, deriv_const] using hd

private theorem free_step_old_rows {N : ℕ}
    (H WH : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (Z : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hWH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ WH)
    (hZ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (w : Fin m → FreeHopfProduct C → ℝ)
    (hw : ∀ i, ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ (w i))
    (hfirst : ∀ x i, inner ℝ (freeHopfDeriv C i.castSucc H x) (WH x) = w i x)
    (hcommH : ∀ x (i j : Fin m),
      freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc H) x =
        freeHopfDeriv C j.castSucc (freeHopfDeriv C i.castSucc H) x)
    (hsecondAll : ∀ x (i j : Fin m),
      2 * inner ℝ (freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc H) x) (WH x) =
        freeHopfDeriv C i.castSucc (w j) x + freeHopfDeriv C j.castSucc (w i) x +
        inner ℝ (freeHopfDeriv C i.castSucc Z x) (freeHopfDeriv C j.castSucc Z x)) :
    ∀ x (i j : Fin m),
      inner ℝ (freeHopfDeriv C i.castSucc H x) (freeHopfDeriv C j.castSucc WH x) +
        inner ℝ (freeHopfDeriv C i.castSucc WH x) (freeHopfDeriv C j.castSucc H x) +
        inner ℝ (freeHopfDeriv C i.castSucc Z x) (freeHopfDeriv C j.castSucc Z x) = 0 := by
  have hderiv (i : Fin (m + 1)) :
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ (freeHopfDeriv C i H) :=
    contMDiff_orbitDeriv _ (freeHopfProductFlow_contMDiff C i) H hH
  let D (i : Fin m) := freeHopfGeneratorSection C i.castSucc
  have hfirstD (x : FreeHopfProduct C) (i : Fin m) :
      inner ℝ (balancedDirectionalDerivative H (D i) x) (WH x) = w i x := by
    rw [free_step_directional C H hH]
    exact hfirst x i
  have hDH (j : Fin m) : balancedDirectionalDerivative H (D j) =
      freeHopfDeriv C j.castSucc H := funext fun x ↦ free_step_directional C H hH _ x
  have hcommD (x : FreeHopfProduct C) (i j : Fin m) :
      balancedDirectionalDerivative (balancedDirectionalDerivative H (D j)) (D i) x =
        balancedDirectionalDerivative (balancedDirectionalDerivative H (D i)) (D j) x := by
    rw [hDH j, hDH i, free_step_directional C _ (hderiv j.castSucc),
      free_step_directional C _ (hderiv i.castSucc)]
    exact hcommH x i j
  have hsecondD (x : FreeHopfProduct C) (i j : Fin m) :
      2 * inner ℝ
          (balancedDirectionalDerivative (balancedDirectionalDerivative H (D j)) (D i) x)
          (WH x) =
        balancedScalarDirectionalDerivative (w j) (D i) x +
          balancedScalarDirectionalDerivative (w i) (D j) x +
          inner ℝ (balancedDirectionalDerivative Z (D i) x)
            (balancedDirectionalDerivative Z (D j) x) := by
    rw [hDH j]
    dsimp only [D]
    rw [free_step_directional C (freeHopfDeriv C j.castSucc H)
        (hderiv j.castSucc) i.castSucc x,
      free_step_scalar_directional C (w j) (hw j) i.castSucc x,
      free_step_scalar_directional C (w i) (hw i) j.castSucc x,
      free_step_directional C Z hZ i.castSucc x, free_step_directional C Z hZ j.castSucc x]
    exact hsecondAll x i j
  have hold := free_old_metric_rows_cancel H WH Z hH hWH hZ D w hfirstD hcommD hsecondD
  have holdRaw (x : FreeHopfProduct C) (i j : Fin m) :
      inner ℝ (freeHopfDeriv C i.castSucc H x) (freeHopfDeriv C j.castSucc WH x) +
        inner ℝ (freeHopfDeriv C i.castSucc WH x) (freeHopfDeriv C j.castSucc H x) +
        inner ℝ (freeHopfDeriv C i.castSucc Z x) (freeHopfDeriv C j.castSucc Z x) = 0 := by
    have hh := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ ↦ A i j) (hold x)
    change inner ℝ (balancedDirectionalDerivative H (D i) x)
        (balancedDirectionalDerivative WH (D j) x) +
      inner ℝ (balancedDirectionalDerivative WH (D i) x)
        (balancedDirectionalDerivative H (D j) x) +
      inner ℝ (balancedDirectionalDerivative Z (D i) x)
        (balancedDirectionalDerivative Z (D j) x) = 0 at hh
    dsimp only [D] at hh
    rw [free_step_directional C H hH i.castSucc x,
      free_step_directional C WH hWH j.castSucc x,
      free_step_directional C WH hWH i.castSucc x,
      free_step_directional C H hH j.castSucc x,
      free_step_directional C Z hZ i.castSucc x,
      free_step_directional C Z hZ j.castSucc x] at hh
    exact hh
  exact holdRaw

/-- The actual whole-product displacement data construct one native smooth W with
the complete second-order metric cancellation. Define the actual e=|XZ|² and g_i
=inner(Y_iZ,XZ), then use the already proved literal b/u/w_i formulas. The actual
old free pairing lift constructs W_H. Put W=(W_H,uv+bJv,0) in the single shared l2
target block. The actual old pairing derivatives cancel all old rows, the basic old
columns and genuine planar derivative cancel mixed rows, and the genuine active
planar computation cancels the active row, including κ=0. Native generator/orbit
identities identify these with the original partial Gram variation.

The hypotheses are actual intermediate induction data, not desired W, a pairing
inverse, or a complete cancellation equation. The final thm:free discharges old
freeness from its induction hypothesis, source-factor basicness and commutation from
the genuine product geometry, and the mixed periods from W2's actual Z construction.
Source: the complete second-cancellation construction in lines 470–475. -/
theorem free_induction_second_correction_exists
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (f : FreeHopfProduct C → Planar)
    (Z : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
    (κ : FreeHopfProduct C → ℝ)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hZ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Z)
    (hκ : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hHbasic : ∀ t x, H (freeHopfProductFlow C (Fin.last m) t x) = H x)
    (hfbasic : ∀ (i : Fin m) t x, f (freeHopfProductFlow C i.castSucc t x) = f x)
    (hind : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (fun i : Fin m ↦ freeHopfProductFlow C i.castSucc) H x))
    (hcommH : ∀ x (i j : Fin m),
      freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc H) x =
        freeHopfDeriv C j.castSucc (freeHopfDeriv C i.castSucc H) x)
    (hunit : ∀ x, ‖freeHopfDeriv C (Fin.last m) f x‖ = 1)
    (hacc : ∀ x,
      freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m) f) x =
        κ x • planarQuarterTurn (freeHopfDeriv C (Fin.last m) f x))
    (hn : ∀ x, ∃ s : ℝ, κ (freeHopfProductFlow C (Fin.last m) s x) ≠ 0)
    (hperiod : ∀ (i : Fin m) x, orbitAverage (freeHopfProductFlow C (Fin.last m))
      (fun y ↦ inner ℝ (freeHopfDeriv C i.castSucc Z y)
        (freeHopfDeriv C (Fin.last m) Z y)) x = 0) :
    ∃ W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))),
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W ∧
      ∀ x, freeMetricCrossTerm (fun y ↦ freeInductionBlock K m (H y) (f y) 0) W
          (fun i ↦ freeHopfGeneratorSection C i) x +
        balancedGeometry Z hZ (fun i ↦ freeHopfGeneratorSection C i) x = 0 := by
  let R := freeHopfProductSmoothFlow C (Fin.last m)
  let S (i : Fin m) := freeHopfProductSmoothFlow C i.castSucc
  let v := freeHopfDeriv C (Fin.last m) f
  let e := freeCancellationEnergy R.flow Z
  let g (i : Fin m) (x : FreeHopfProduct C) : ℝ :=
    inner ℝ (freeHopfDeriv C i.castSucc Z x) (freeHopfDeriv C (Fin.last m) Z x)
  have hderiv {N : ℕ} (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
      (hF : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
      (i : Fin (m + 1)) :
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C i F) :=
    contMDiff_orbitDeriv _ (freeHopfProductFlow_contMDiff C i) F hF
  have hv := hderiv f hf (Fin.last m)
  have he := freeCancellationEnergy_contMDiff R Z hZ
  have hg (i : Fin m) : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ (g i) :=
    (contDiff_inner (𝕜 := ℝ)).contMDiff.comp
      ((hderiv Z hZ i.castSucc).prodMk_space (hderiv Z hZ (Fin.last m)))
  have hcomm (i : Fin m) (t s : ℝ) (x : FreeHopfProduct C) :
      R.flow t ((S i).flow s x) = (S i).flow s (R.flow t x) :=
    freeHopfProductFlow_commute C (Fin.last m) i.castSucc t s x
  let u := freeCancellationU R.flow κ e
  let b := freeCancellationB R.flow κ e
  let w (i : Fin m) := freeCancellationW R.flow (S i).flow κ e (g i)
  have hu := freeCancellationU_contMDiff R κ e hκ he hn
  have hb := freeCancellationB_contMDiff R κ e hκ he hn
  have hw (i : Fin m) : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ (w i) :=
    freeCancellationW_contMDiff R (S i) κ e (g i) hκ he (hg i) hn
  obtain ⟨WH, hWH, hfirst, hsecond⟩ := free_old_second_correction_exists S H hH hind w hw Z hZ
  change (∀ x i, inner ℝ (freeHopfDeriv C i.castSucc H x) (WH x) = w i x) at hfirst
  change (∀ x (ij : {p : Fin m × Fin m // p.1 ≤ p.2}),
    2 * inner ℝ (freeHopfDeriv C ij.val.1.castSucc
      (freeHopfDeriv C ij.val.2.castSucc H) x) (WH x) =
      freeHopfDeriv C ij.val.1.castSucc (w ij.val.2) x +
        freeHopfDeriv C ij.val.2.castSucc (w ij.val.1) x +
        inner ℝ (freeHopfDeriv C ij.val.1.castSucc Z x)
          (freeHopfDeriv C ij.val.2.castSucc Z x)) at hsecond
  let p := freePlanarSecondCorrection v u b
  have hp := freePlanarSecondCorrection_contMDiff v u b hv hu hb
  let W (x : FreeHopfProduct C) := freeInductionBlock K m (WH x) (p x) 0
  have hW : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W :=
    freeInductionBlock_contMDiff K m WH p (fun _ ↦ 0) hWH hp contMDiff_const
  have hHlast (x : FreeHopfProduct C) : freeHopfDeriv C (Fin.last m) H x = 0 := by
    unfold freeHopfDeriv orbitDeriv
    simp only [hHbasic, deriv_const]
  have hfold (i : Fin m) (x : FreeHopfProduct C) : freeHopfDeriv C i.castSucc f x = 0 := by
    unfold freeHopfDeriv orbitDeriv
    simp only [hfbasic, deriv_const]
  have hvbasic (i : Fin m) (t : ℝ) (x : FreeHopfProduct C) :
      v ((S i).flow t x) = v x := by
    change deriv (fun s : ℝ ↦ f (R.flow s ((S i).flow t x))) 0 =
      deriv (fun s : ℝ ↦ f (R.flow s x)) 0
    congr 1
    funext s
    rw [hcomm i s t x]
    exact hfbasic i t (R.flow s x)
  have hHibasic (i : Fin m) (t : ℝ) (x : FreeHopfProduct C) :
      freeHopfDeriv C i.castSucc H (R.flow t x) = freeHopfDeriv C i.castSucc H x := by
    unfold freeHopfDeriv orbitDeriv
    congr 1
    funext s
    change H (freeHopfProductFlow C i.castSucc s
      (freeHopfProductFlow C (Fin.last m) t x)) = H (freeHopfProductFlow C i.castSucc s x)
    rw [freeHopfProductFlow_commute C i.castSucc (Fin.last m) s t x, hHbasic]
  have hmixed (i : Fin m) (x : FreeHopfProduct C) :
      inner ℝ (freeHopfDeriv C i.castSucc H x) (freeHopfDeriv C (Fin.last m) WH x) +
          inner ℝ (v x) (freeHopfDeriv C i.castSucc p x) + g i x = 0 := by
    have hi := free_basic_pairing_derivative R (freeHopfDeriv C i.castSucc H) WH (w i)
      hWH (hw i) (hHibasic i) (fun y ↦ hfirst y i) x
    have hpmean := freePlanarSecondCorrection_mixed_cancel R (S i) (hcomm i) v κ e (g i)
      hv hκ he (hg i) hn hunit (hvbasic i) (hperiod i) x
    change inner ℝ (freeHopfDeriv C i.castSucc H x) (freeHopfDeriv C (Fin.last m) WH x) +
      inner ℝ (v x) (freeHopfDeriv C i.castSucc p x) + g i x = 0
    change inner ℝ (freeHopfDeriv C i.castSucc H x)
      (freeHopfDeriv C (Fin.last m) WH x) = freeHopfDeriv C (Fin.last m) (w i) x at hi
    change freeHopfDeriv C (Fin.last m) (w i) x +
      inner ℝ (v x) (freeHopfDeriv C i.castSucc p x) = -g i x at hpmean
    rw [hi, hpmean]
    ring
  have hsecondAll (x : FreeHopfProduct C) (i j : Fin m) :
      2 * inner ℝ (freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc H) x) (WH x) =
        freeHopfDeriv C i.castSucc (w j) x + freeHopfDeriv C j.castSucc (w i) x +
        inner ℝ (freeHopfDeriv C i.castSucc Z x) (freeHopfDeriv C j.castSucc Z x) := by
    by_cases hij : i ≤ j
    · exact hsecond x ⟨(i, j), hij⟩
    · have hs := hsecond x ⟨(j, i), le_of_not_ge hij⟩
      rw [hcommH x i j]
      simpa only [add_comm, real_inner_comm] using hs
  have holdRaw := free_step_old_rows C H WH Z hH hWH hZ w hw hfirst hcommH hsecondAll
  refine ⟨W, hW, ?_⟩
  intro x
  ext i j
  change inner ℝ
      (balancedDirectionalDerivative (fun y ↦ freeInductionBlock K m (H y) (f y) 0)
        (freeHopfGeneratorSection C i) x)
      (balancedDirectionalDerivative W (freeHopfGeneratorSection C j) x) +
    inner ℝ (balancedDirectionalDerivative W (freeHopfGeneratorSection C i) x)
      (balancedDirectionalDerivative (fun y ↦ freeInductionBlock K m (H y) (f y) 0)
        (freeHopfGeneratorSection C j) x) +
    inner ℝ (balancedDirectionalDerivative Z (freeHopfGeneratorSection C i) x)
      (balancedDirectionalDerivative Z (freeHopfGeneratorSection C j) x) = 0
  dsimp only [W]
  rw [free_step_block_directional C H f hH hf i x,
    free_step_block_directional C WH p hWH hp j x,
    free_step_block_directional C WH p hWH hp i x,
    free_step_block_directional C H f hH hf j x,
    free_step_directional C Z hZ i x, free_step_directional C Z hZ j x]
  simp only [freeInductionBlock_inner, inner_zero_left, add_zero]
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · have ha := freePlanarSecondCorrection_active_cancel R v κ e hv hκ he hn hunit hacc x
      rw [hHlast x]
      simp only [inner_zero_left, inner_zero_right, zero_add]
      change inner ℝ (v x) (freeHopfDeriv C (Fin.last m) p x) +
        inner ℝ (freeHopfDeriv C (Fin.last m) p x) (v x) +
        inner ℝ (freeHopfDeriv C (Fin.last m) Z x)
          (freeHopfDeriv C (Fin.last m) Z x) = 0
      rw [real_inner_comm (v x) (freeHopfDeriv C (Fin.last m) p x),
        real_inner_self_eq_norm_sq]
      change 2 * inner ℝ (v x) (freeHopfDeriv C (Fin.last m) p x) =
        -‖freeHopfDeriv C (Fin.last m) Z x‖ ^ 2 at ha
      linarith
    · rw [hHlast x, hfold j x]
      simp only [inner_zero_left, inner_zero_right, zero_add, add_zero]
      have hm := hmixed j x
      rw [real_inner_comm (freeHopfDeriv C j.castSucc H x)
          (freeHopfDeriv C (Fin.last m) WH x),
        real_inner_comm (freeHopfDeriv C j.castSucc Z x)
          (freeHopfDeriv C (Fin.last m) Z x)]
      change inner ℝ (v x) (freeHopfDeriv C j.castSucc p x) +
        inner ℝ (freeHopfDeriv C j.castSucc H x) (freeHopfDeriv C (Fin.last m) WH x) +
        g j x = 0
      linarith
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [hHlast x, hfold i x]
      simp only [inner_zero_left, inner_zero_right, zero_add, add_zero]
      rw [real_inner_comm (v x) (freeHopfDeriv C i.castSucc p x)]
      exact hmixed i x
    · rw [hfold i x, hfold j x]
      simp only [inner_zero_left, inner_zero_right, add_zero]
      exact holdRaw x i j

/-- The whole actual W construction requires no supplied commutation equation.
Apply the accepted genuine orbit-lift pushforward to the accepted native lift/Schwarz
theorem. It gives the old second-column commutation for this very H, and the preceding
actual construction supplies W with all rows cancelled. This merely consumes the actual
W1 geometry; no pushforward, formal commutation or desired W is an input.
Source: second cancellation in thm:free, lines 470–475. -/
theorem free_induction_second_correction
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin K))
    (f : FreeHopfProduct C → Planar)
    (Z : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
    (κ : FreeHopfProduct C → ℝ)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hZ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Z)
    (hκ : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hHbasic : ∀ t x, H (freeHopfProductFlow C (Fin.last m) t x) = H x)
    (hfbasic : ∀ (i : Fin m) t x, f (freeHopfProductFlow C i.castSucc t x) = f x)
    (hind : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (fun i : Fin m ↦ freeHopfProductFlow C i.castSucc) H x))
    (hunit : ∀ x, ‖freeHopfDeriv C (Fin.last m) f x‖ = 1)
    (hacc : ∀ x,
      freeHopfDeriv C (Fin.last m) (freeHopfDeriv C (Fin.last m) f) x =
        κ x • planarQuarterTurn (freeHopfDeriv C (Fin.last m) f x))
    (hn : ∀ x, ∃ s : ℝ, κ (freeHopfProductFlow C (Fin.last m) s x) ≠ 0)
    (hperiod : ∀ (i : Fin m) x, orbitAverage (freeHopfProductFlow C (Fin.last m))
      (fun y ↦ inner ℝ (freeHopfDeriv C i.castSucc Z y)
        (freeHopfDeriv C (Fin.last m) Z y)) x = 0) :
    ∃ W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))),
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W ∧
      ∀ x, freeMetricCrossTerm (fun y ↦ freeInductionBlock K m (H y) (f y) 0) W
          (fun i ↦ freeHopfGeneratorSection C i) x +
        balancedGeometry Z hZ (fun i ↦ freeHopfGeneratorSection C i) x = 0 := by
  have hcommH (x : FreeHopfProduct C) (i j : Fin m) :
      freeHopfDeriv C i.castSucc (freeHopfDeriv C j.castSucc H) x =
        freeHopfDeriv C j.castSucc (freeHopfDeriv C i.castSucc H) x :=
    freeHopfDeriv_commute_euclidean C H hH i.castSucc j.castSucc x
  exact free_induction_second_correction_exists C H f Z κ hH hf hZ hκ hHbasic hfbasic
    hind hcommH hunit hacc hn hperiod

#print axioms free_induction_second_correction_exists
#print axioms free_induction_second_correction

end GlobalEmbedding.Paper
