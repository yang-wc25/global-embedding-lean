import GlobalEmbedding.Paper.IncrementsActualModeSize
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-!
# Actual joint finite-mode compatibility and total weighted jets

Source: `main.tex`, lem:increments594–650, equation6.2 and finite parameters.
DAG: `increments-mode-joint-quantitative-finite-u`. Exclusive worker W2.
ONE stage2 endpoint for ROOT exact lock; its named proof hole is expected.
-/

noncomputable section
open Manifold
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ
local notation "X" => Ep × D

/-- The SAME actual spatial finite mode formula is jointly smooth and has the
explicit TOTAL weighted jet bound on the original open parameter/spatial domain.
Its local equality with the existing total-source finite formula uses actual A/B
from the SAME F/hF/c and constant native spatial precomposition; B is unchanged.

Natural-language proof, pending ROOT exact lock: take the native fixed inclusion
inc=inr:D→Ep×D. Let P send a full derivative jet to its composition with inc;
let Q precompose the actual spatial coefficient A with P, so Ahat=Q composed A.
Native compL/flip/inr norm bounds give norm P and norm Q at most one, and native
constant-CLM calculus transfers joint smoothness and every TOTAL coefficient jet
bound to Ahat without loss. Reuse generic actual iterate/sum smoothness on X.
Induct only for compatibility: on the original open O, the preceding iterate's
EqOn gives equality of genuine local slice derivative germs. The accepted spatial
jet bridge identifies that slice derivative with total fderiv followed by inc.
Thus each SAME actual slice step equals the generic lifted step locally, and the
literal finite sum is EqOn with the existing total-source finite sum. This local
equality also transfers joint smoothness. Actual A/B complex scalar commutation,
with native precomposition, discharges the generic finite-sum theorem's scalar
hypotheses. Apply that accepted weighted-jet theorem on X, use norm(tau/i)=tau,
and transfer total jets by open-domain equality of germs. No weighted induction,
finite telescoping or existing 4fc smoothness induction is repeated.

The input k is a genuine source, not a supplied solution or output estimate; the
accepted 4fc computed real/imaginary source is its explicit geometric caller.
All input jet derivatives below are on X and retain every mixed parameter
direction. Original conditioning/profile suppliers, joint R/transport and the
all-order finite-input validity threshold remain genuine caller obligations.
The length/n/tau are fixed before observation j; tau is an external scalar, not
an auxiliary parameter coordinate. Empty O/S and zero parameter dimension are
allowed, and length zero gives the same zero finite sum. No new norm, carrier,
solver, global parameter extension or original final-target hypothesis is added.
Source: original equation6.2 finite polynomial and auxiliary-parameter clause. -/
theorem incrementsModeJointFiniteU_compatible_contDiffOn_scaled_jet
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (k : X → Cdata)
    (n length : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hk : ContDiffOn ℝ ∞ k O)
    (tau ell Mb Kb : ℝ) (htau : 0 < tau) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X ↦ incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2)
      z‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X ↦ incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2)
      z‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k z‖ ≤ Kb) :
    let Ap := fun p ↦ incrementsModeComplexFirstOrderA (F p) (hF p) (c p)
    let Bp := fun p ↦ incrementsModeComplexFirstOrderB (F p) (hF p) (c p)
    let A : X → (D →L[ℝ] Cdata) →L[ℝ] Cdata := fun z ↦ Ap z.1 z.2
    let B : X → Cdata →L[ℝ] Cdata := fun z ↦ Bp z.1 z.2
    let inc : D →L[ℝ] X := ContinuousLinearMap.inr ℝ Ep D
    let P : (X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata) :=
      (ContinuousLinearMap.compL ℝ D X Cdata).flip inc
    let Q : ((D →L[ℝ] Cdata) →L[ℝ] Cdata) →L[ℝ]
        ((X →L[ℝ] Cdata) →L[ℝ] Cdata) :=
      ContinuousLinearMap.flip (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
        (E' := (D →L[ℝ] Cdata) →L[ℝ] Cdata)
        (F' := (X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata))
        (G' := (X →L[ℝ] Cdata) →L[ℝ] Cdata)
        (ContinuousLinearMap.compL ℝ (X →L[ℝ] Cdata) (D →L[ℝ] Cdata) Cdata) P
    let Ahat : X → (X →L[ℝ] Cdata) →L[ℝ] Cdata := fun z ↦ Q (A z)
    let alpha := (tau : ℂ) / Complex.I
    let U : X → Cdata := fun z ↦
      incrementsActualModeSum (Ap z.1) (Bp z.1) alpha length (fun x ↦ k (z.1, x)) z.2
    Set.EqOn U (incrementsActualModeSum Ahat B alpha length k) O ∧
      ContDiffOn ℝ ∞ U O ∧
      ∀ j, j + length ≤ n → ∀ z ∈ S,
        ell ^ j * ‖iteratedFDeriv ℝ j U z‖ ≤
          tau * Kb * ∑ r ∈ Finset.range length,
            ((2 * 2 ^ n * Mb) * tau / ell) ^ r := by
  classical
  dsimp only
  let Ap := fun p ↦ incrementsModeComplexFirstOrderA (F p) (hF p) (c p)
  let Bp := fun p ↦ incrementsModeComplexFirstOrderB (F p) (hF p) (c p)
  let A : X → (D →L[ℝ] Cdata) →L[ℝ] Cdata := fun z ↦ Ap z.1 z.2
  let B : X → Cdata →L[ℝ] Cdata := fun z ↦ Bp z.1 z.2
  let inc : D →L[ℝ] X := ContinuousLinearMap.inr ℝ Ep D
  let P : (X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata) :=
    (ContinuousLinearMap.compL ℝ D X Cdata).flip inc
  let : SeminormedAddCommGroup ((D →L[ℝ] Cdata) →L[ℝ] Cdata) :=
    (inferInstance : NormedAddCommGroup ((D →L[ℝ] Cdata) →L[ℝ] Cdata)).toSeminormedAddCommGroup
  let : SeminormedAddCommGroup ((X →L[ℝ] Cdata) →L[ℝ] Cdata) :=
    (inferInstance : NormedAddCommGroup ((X →L[ℝ] Cdata) →L[ℝ] Cdata)).toSeminormedAddCommGroup
  let : SeminormedAddCommGroup ((X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata)) :=
    (inferInstance : NormedAddCommGroup
      ((X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata))).toSeminormedAddCommGroup
  let Q := (ContinuousLinearMap.flipₗᵢ ℝ
    ((D →L[ℝ] Cdata) →L[ℝ] Cdata)
    ((X →L[ℝ] Cdata) →L[ℝ] (D →L[ℝ] Cdata))
    ((X →L[ℝ] Cdata) →L[ℝ] Cdata))
    (ContinuousLinearMap.compL ℝ (X →L[ℝ] Cdata) (D →L[ℝ] Cdata) Cdata) P
  let Ahat : X → (X →L[ℝ] Cdata) →L[ℝ] Cdata := fun z ↦ Q (A z)
  let alpha := (tau : ℂ) / Complex.I
  let U : X → Cdata := fun z ↦
    incrementsActualModeSum (Ap z.1) (Bp z.1) alpha length (fun x ↦ k (z.1, x)) z.2
  change Set.EqOn U (incrementsActualModeSum Ahat B alpha length k) O ∧
    ContDiffOn ℝ ∞ U O ∧ _
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖f.comp inc‖ ≤ 1 * ‖f‖
    calc
      _ ≤ ‖f‖ * ‖inc‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by
        simpa [inc] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := Ep) (F := D))
          (norm_nonneg f)
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖f.comp P‖ ≤ 1 * ‖f‖
    calc
      _ ≤ ‖f‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hP (norm_nonneg f)
  have hAh : ContDiffOn ℝ ∞ Ahat O := hA.clm_comp contDiffOn_const
  have hAhb : ∀ i ≤ n, ∀ z ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i Ahat z‖ ≤ Mb := by
    intro i hi z hz
    have hd := Q.norm_iteratedFDeriv_comp_left
      (hA.contDiffAt (hO.mem_nhds (hSO hz))) (by simp : (i : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ i * (‖Q‖ * ‖iteratedFDeriv ℝ i A z‖) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ ell ^ i * ‖iteratedFDeriv ℝ i A z‖ := by
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) hQ
      _ ≤ Mb := hAb i hi z hz
  let W (r : ℕ) : X → Cdata := (incrementsActualModeStep Ahat B alpha)^[r] k
  let vs (r : ℕ) (p : Ep) : D → Cdata :=
    (incrementsActualModeStep (Ap p) (Bp p) alpha)^[r] (fun x ↦ k (p, x))
  have hWs (r : ℕ) : ContDiffOn ℝ ∞ (W r) O :=
    increments_actual_mode_iterate_contDiffOn Ahat B alpha r k O hO hAh hB hk
  have he (r : ℕ) : ∀ z ∈ O, vs r z.1 z.2 = W r z := by
    induction r with
    | zero => intro z hz; rfl
    | succ r ih =>
      intro z hz
      have hg : vs r z.1 =ᶠ[nhds z.2] (fun x ↦ W r (z.1, x)) := by
        filter_upwards [(hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
          with x hx
        exact ih (z.1, x) hx
      have hd := (incrementsJointSpatialJets_bridge (W r) O hO (hWs r)).1 z hz
      change ((incrementsActualModeStep (Ap z.1) (Bp z.1) alpha)^[r + 1]
        (fun x ↦ k (z.1, x))) z.2 =
        ((incrementsActualModeStep Ahat B alpha)^[r + 1] k) z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (-alpha) • (Bp z.1 z.2 (vs r z.1 z.2) +
        Ap z.1 z.2 (fderiv ℝ (vs r z.1) z.2)) =
        (-alpha) • (B z (W r z) + Ahat z (fderiv ℝ (W r) z))
      rw [ih z hz, hg.fderiv_eq, hd]
      rfl
  have heU : Set.EqOn U (incrementsActualModeSum Ahat B alpha length k) O := by
    intro z hz
    change alpha • (∑ r ∈ Finset.range length, vs r z.1 z.2) =
      alpha • (∑ r ∈ Finset.range length, W r z)
    congr 1
    exact Finset.sum_congr rfl (fun r _ ↦ he r z hz)
  have hUs : ContDiffOn ℝ ∞ U O :=
    (increments_actual_mode_sum_contDiffOn Ahat B alpha length k O hO hAh hB hk).congr heU
  refine ⟨heU, hUs, ?_⟩
  intro j hj z hz
  have hg : U =ᶠ[nhds z] incrementsActualModeSum Ahat B alpha length k := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact heU hw
  rw [(hg.iteratedFDeriv ℝ j).self_of_nhds]
  have hn : ‖alpha‖ = tau := by simp [alpha, abs_of_pos htau]
  have ha : alpha ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact htau)
  have hAc : ∀ w ∈ O, ∀ jet, Ahat w (alpha • jet) = alpha • Ahat w jet := by
    intro w hw jet
    change Ap w.1 w.2 ((alpha • jet).comp inc) =
      alpha • Ap w.1 w.2 (jet.comp inc)
    rw [ContinuousLinearMap.smul_comp]
    exact incrementsModeComplexFirstOrderA_smul (F w.1) (hF w.1) (c w.1) w.2 alpha _
  have hBc : ∀ w ∈ O, ∀ v, B w (alpha • v) = alpha • B w v := by
    intro w hw v
    exact incrementsModeComplexFirstOrderB_smul (F w.1) (hF w.1) (c w.1) w.2 alpha v
  simpa only [hn] using increments_actual_mode_sum_scaled_jet n length O S hO hSO
    Ahat B alpha ha k hAh hB hk hAc hBc ell Mb Kb hell hell1 hM hK hAhb hBb hkb
    j hj z hz

end GlobalEmbedding.Paper
