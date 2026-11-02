import Probes.ActualHomogeneousSource

/-!
# The primitive normal amplitude supplies the actual homogeneous source

The normal vector is the genuine subtype in the original normal bundle.
The amplitude is literally -delta*tau/lambda² times chi times nu. Its joint
slow jets are derived from the actual cutoff and normal-field jets, and fed
into the original mode source with h=0. No bound on the desired source is
assumed. All coordinate and forcing norms remain in the constants.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualProbeNormalAmplitude
    (F : Ep → M → V) (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
    (delta tau lambda : ℝ) (p : Ep) (x : D) : normalSpace (I := I) (F p) (chart p x) :=
  (-(delta*tau) / lambda^2) • (chi (p,x) • nu p x)

def probeNormalAmplitudeConstant (j : ℕ) (lambda Bchi Bnu : ℝ) : ℝ :=
  (2^j * Bchi * Bnu) / lambda^2

theorem probeNormalAmplitudeConstant_nonneg (j : ℕ) (lambda : ℝ) {Bchi Bnu : ℝ}
    (hchi : 0 ≤ Bchi) (hnu : 0 ≤ Bnu) :
    0 ≤ probeNormalAmplitudeConstant j lambda Bchi Bnu := by
  unfold probeNormalAmplitudeConstant
  positivity

/-- Actual cutoff/normal jets imply all required amplitude jets on the same
joint parameter/source domain, with the original delta*tau scale. -/
theorem actualProbeNormalAmplitude_weighted_jets
    (F : Ep → M → V) (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
    (O : Set X) (hO : IsOpen O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (j : ℕ) (ell delta tau lambda Bchi Bnu : ℝ)
    (hell : 0 ≤ ell) (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hchib : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ j, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun y : X => (nu y.1 y.2 : V)) z‖ ≤ Bnu) :
    let vf := actualProbeNormalAmplitude F chart chi nu delta tau lambda
    ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun y : X => (vf y.1 y.2 : V)) z‖ ≤
        probeNormalAmplitudeConstant j lambda Bchi Bnu * (delta*tau) := by
  dsimp only
  let v : X → V := fun z => chi z • (nu z.1 z.2 : V)
  have hv : ContDiffOn ℝ ∞ v O := hchi.smul hnu
  have hvf : (fun z : X => (actualProbeNormalAmplitude F chart chi nu delta tau lambda z.1 z.2 : V)) =
      fun z => (-(delta*tau)/lambda^2) • v z := rfl
  rw [hvf]
  refine ⟨hv.const_smul _, ?_⟩
  intro k hk z hz
  have hbil := slow_bilinear_jet_bound_norm
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
    O hO chi (fun y : X => (nu y.1 y.2 : V)) hchi hnu k ell Bchi Bnu hell z hz
    (fun a ha => hchib a (ha.trans hk) z hz) (fun a ha => hnub a (ha.trans hk) z hz)
  have hbase : ell^k * ‖iteratedFDeriv ℝ k v z‖ ≤ 2^j * Bchi * Bnu := by
    apply hbil.trans
    apply mul_le_mul_of_nonneg_right _ hBnu
    calc
      _ ≤ 2^k * (1 * Bchi) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le hBchi) (by positivity)
      _ ≤ 2^j * Bchi := by
        simpa using mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hBchi
  have hs : ContDiffAt ℝ k v z := (hv.contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  rw [iteratedFDeriv_const_smul_apply' hs, norm_smul, Real.norm_eq_abs,
    abs_div, abs_neg, abs_of_nonneg (mul_nonneg hdelta htau), abs_of_nonneg (sq_nonneg lambda)]
  unfold probeNormalAmplitudeConstant
  convert mul_le_mul_of_nonneg_left hbase (div_nonneg (mul_nonneg hdelta htau) (sq_nonneg lambda)) using 1 <;> ring

/-- Primitive true-B, cutoff and actual normal-field profiles produce the
actual original homogeneous source at scale delta*tau. -/
theorem actualProbeHomogeneousSource_weighted_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
    (O : Set X) (hO : IsOpen O)
    (hB : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (j : ℕ) (ell delta tau lambda MB Bchi Bnu : ℝ)
    (hell : 0 ≤ ell) (hdelta : 0 ≤ delta) (htau : 0 ≤ tau)
    (hMB : 0 ≤ MB) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBb : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ j, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun y : X => (nu y.1 y.2 : V)) z‖ ≤ Bnu) :
    let vf := actualProbeNormalAmplitude F chart chi nu delta tau lambda
    ContDiffOn ℝ ∞ (actualHomogeneousSource F hF chart vf) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (actualHomogeneousSource F hF chart vf) z‖ ≤
        homogeneousSourceConstant m N j MB (probeNormalAmplitudeConstant j lambda Bchi Bnu) * (delta*tau) := by
  have ha := actualProbeNormalAmplitude_weighted_jets F chart chi nu O hO hchi hnu j
    ell delta tau lambda Bchi Bnu hell hdelta htau hBchi hBnu hchib hnub
  exact actualHomogeneousSource_weighted_jets F hF chart
    (actualProbeNormalAmplitude F chart chi nu delta tau lambda) O hO hB ha.1 j ell MB
    (probeNormalAmplitudeConstant j lambda Bchi Bnu) (delta*tau) hell hMB
    (probeNormalAmplitudeConstant_nonneg j lambda hBchi hBnu) (mul_nonneg hdelta htau) hBb ha.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeNormalAmplitude_weighted_jets
#print axioms GlobalEmbedding.Continuation.actualProbeHomogeneousSource_weighted_jets
