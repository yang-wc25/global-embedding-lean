import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# All actual Frechet derivatives commute with the source Gaussian convolution

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof line 520. The convolution is smooth of every finite order, and its actual iterated
Frechet derivatives are Gaussian convolutions of the actual derivatives of the original map.
-/

open MeasureTheory Filter Metric Set
open scoped Topology Convolution ContDiff

namespace GlobalEmbedding.Paper

universe u

/-- A smooth compactly supported map has a smooth source Gaussian convolution, and every
actual iterated Frechet derivative commutes with that convolution in its actual multilinear
operator space, including order zero and domain dimension zero.

Source: Proposition `prop:collar`, proof line 520; all-order derivative-convolution detail.
Write the actual source integral as convolution with scalar multiplication. The Gaussian is
continuous and hence locally integrable; the actual right factor has compact support and is
C∞. Mathlib's convolution theorem gives genuine C∞ regularity. Induct on the derivative order.
At order zero, transport the integral through the canonical zero-argument currying equivalence.
At the successor, the nth derivative of the original map is still smooth and compactly
supported. Apply the actual derivative-of-convolution theorem to that map, and transport its
actual integral through the canonical left currying equivalence. This identifies the actual
(n+1)st multilinear derivative without coordinate choices or a finite derivative cutoff.
No analyticity or compact support of the Gaussian is assumed. -/
theorem collar_gaussian_derivative_convolution
    {d : ℕ} {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (ε : ℝ) (_hε : 0 < ε) (f : EuclideanSpace ℝ (Fin d) → W)
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    let K : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
      (Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / ε)
    let G : EuclideanSpace ℝ (Fin d) → W := fun x ↦ ∫ y, K (x - y) • f y
    ContDiff ℝ ∞ G ∧ ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      iteratedFDeriv ℝ n G x = ∫ y, K (x - y) • iteratedFDeriv ℝ n f y := by
  let V := EuclideanSpace ℝ (Fin d)
  let K : V → ℝ := fun x ↦
    (Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / ε)
  let L (T : Type u) [NormedAddCommGroup T] [NormedSpace ℝ T] : ℝ →L[ℝ] T →L[ℝ] T :=
    ContinuousLinearMap.lsmul ℝ ℝ
  let H : V → W := K ⋆[L W] f
  have hK : Continuous K :=
    continuous_const.mul (Real.continuous_exp.comp ((continuous_norm.pow 2).neg.div_const ε))
  have hKli : LocallyIntegrable K (volume : Measure V) := hK.locallyIntegrable
  have hH : ContDiff ℝ ∞ H := hcompact.contDiff_convolution_right (L W) hKli hf
  have hEq : (fun x : V ↦ ∫ y, K (x - y) • f y) = H := by
    funext x
    exact (convolution_eq_swap (L W)).symm
  change ContDiff ℝ ∞ (fun x : V ↦ ∫ y, K (x - y) • f y) ∧ _
  rw [hEq]
  refine ⟨hH, ?_⟩
  have hderiv (n : ℕ) : iteratedFDeriv ℝ n H = K ⋆[L (V [×n]→L[ℝ] W)]
      iteratedFDeriv ℝ n f := by
    induction n with
    | zero =>
      funext x
      let e := (continuousMultilinearCurryFin0 ℝ V W).symm.toContinuousLinearEquiv
      change e (∫ y, K y • f (x - y)) = ∫ y, K y • e (f (x - y))
      simpa only [map_smul] using (e.integral_comp_comm (fun y ↦ K y • f (x - y))).symm
    | succ n ih =>
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
      have hg : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (by simp)
      have hd := (hcompact.iteratedFDeriv n).hasFDerivAt_convolution_right
        (L (V [×n]→L[ℝ] W)) hKli hg x
      rw [hd.fderiv]
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ V) W).symm
        |>.toContinuousLinearEquiv
      change e (∫ y, (L (V [×n]→L[ℝ] W)).precompR V (K y)
          (fderiv ℝ (iteratedFDeriv ℝ n f) (x - y))) =
        ∫ y, K y • iteratedFDeriv ℝ (n + 1) f (x - y)
      rw [← e.integral_comp_comm (fun y : V ↦
        (L (V [×n]→L[ℝ] W)).precompR V (K y)
          (fderiv ℝ (iteratedFDeriv ℝ n f) (x - y)))]
      congr 1
  intro n x
  rw [hderiv n]
  exact convolution_eq_swap (L (V [×n]→L[ℝ] W))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_gaussian_derivative_convolution
