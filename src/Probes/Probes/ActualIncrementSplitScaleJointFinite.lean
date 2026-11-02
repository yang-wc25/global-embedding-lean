import Probes.ActualIncrementSplitScaleFinite
import GlobalEmbedding.Paper.IncrementsModeJointQuantitativeFiniteU
import GlobalEmbedding.Paper.IncrementsModeActualFiniteResidual
import Smoothing.WeightedActualOperations

/-! Joint parameter/source bounds for the literal spatial finite solver at
its genuine adapted-coordinate scales. The old exact native spatial lift is
reused on an empty sample set to extract only its qualitative compatibility;
all estimates here use the proved A shift0/B shift1 bound. Thus no false
uniform bound on Gamma or the value coefficient enters the actual solver. -/

noncomputable section
open Manifold GlobalEmbedding.Paper Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ
local notation "X" => Ep × D


theorem actual_increment_joint_mode_sum_split_scale_jets
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
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
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
  have hcompat := incrementsModeJointFiniteU_compatible_contDiffOn_scaled_jet F hF c k
    n length O ∅ hO (by simp) hA hB hk tau ell 0 0 htau hell hell1 le_rfl le_rfl
    (by simp) (by simp) (by simp)
  change Set.EqOn U (incrementsActualModeSum Ahat B alpha length k) O ∧
    ContDiffOn ℝ ∞ U O ∧ _ at hcompat
  refine ⟨hcompat.1,hcompat.2.1,?_⟩
  intro j hj z hz
  have hg : U =ᶠ[nhds z] incrementsActualModeSum Ahat B alpha length k := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact hcompat.1 hw
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
  simpa only [hn] using actual_increment_mode_sum_split_scale_jets n length O S hO hSO
    Ahat B alpha ha k hAh hB hk hAc hBc ell Mb Kb hell hell1 hM hK hAhb hBb hkb
    j hj z hz

theorem actual_increment_joint_residual_split_scale_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (k : X → Cdata)
    (n length : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hk : ContDiffOn ℝ ∞ k O)
    (tau ell Mb Kb : ℝ) (htau : 0 < tau) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k z‖ ≤ Kb) :
    let alpha := (tau : ℂ) / Complex.I
    let U := fun p => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
      (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) alpha length
      (fun x => k (p, x))
    ∀ j, j + length ≤ n → ∀ z ∈ S, ell ^ j * ‖iteratedFDeriv ℝ j
      (fun w : X => alpha⁻¹ • U w.1 w.2 +
        incrementsModeComplexReducedOperator (F w.1) (hF w.1) (c w.1) (U w.1) w.2 - k w) z‖ ≤
      (2 * 2 ^ n * Mb) ^ length * (tau / ell) ^ length * Kb := by
  dsimp only
  let Ap := fun p => incrementsModeComplexFirstOrderA (F p) (hF p) (c p)
  let Bp := fun p => incrementsModeComplexFirstOrderB (F p) (hF p) (c p)
  let A := fun z : X => Ap z.1 z.2
  let B := fun z : X => Bp z.1 z.2
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
  let Ahat := fun z : X => Q (A z)
  let alpha := (tau : ℂ) / Complex.I
  let U := fun p => incrementsActualModeSum (Ap p) (Bp p) alpha length (fun x => k (p, x))
  let Ujoint := fun z : X => U z.1 z.2
  let Uhat := incrementsActualModeSum Ahat B alpha length k
  have hcompat := actual_increment_joint_mode_sum_split_scale_jets F hF c k
    n length O S hO hSO hA hB hk tau ell Mb Kb htau hell hell1 hM hK hAb hBb hkb
  change EqOn Ujoint Uhat O ∧ ContDiffOn ℝ ∞ Ujoint O ∧ _ at hcompat
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro L
    change ‖L.comp inc‖ ≤ 1 * ‖L‖
    calc
      _ ≤ ‖L‖ * ‖inc‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by
        simpa [inc] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := Ep) (F := D)) L.opNorm_nonneg
  have hQ : ‖Q‖ ≤ 1 := by
    apply Q.opNorm_le_bound zero_le_one
    intro L
    change ‖L.comp P‖ ≤ 1 * ‖L‖
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left hP L.opNorm_nonneg)
  have hAh : ContDiffOn ℝ ∞ Ahat O := Q.contDiff.comp_contDiffOn hA
  have hAhb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i Ahat z‖ ≤ Mb := by
    intro i hi z hz
    exact (slow_linear_jet_bound Q O hO A hA i ell Mb hell.le z (hSO hz)
      (hAb i hi z hz)).trans (mul_le_of_le_one_left hM hQ)
  have hAc : ∀ z ∈ O, ∀ jet, Ahat z (alpha • jet) = alpha • Ahat z jet := by
    intro z hz jet
    change Ap z.1 z.2 ((alpha • jet).comp inc) = alpha • Ap z.1 z.2 (jet.comp inc)
    rw [ContinuousLinearMap.smul_comp]
    exact incrementsModeComplexFirstOrderA_smul (F z.1) (hF z.1) (c z.1) z.2 alpha _
  have hBc : ∀ z ∈ O, ∀ v, B z (alpha • v) = alpha • B z v := by
    intro z hz v
    exact incrementsModeComplexFirstOrderB_smul (F z.1) (hF z.1) (c z.1) z.2 alpha v
  have he : EqOn (fun z : X => alpha⁻¹ • U z.1 z.2 +
      incrementsModeComplexReducedOperator (F z.1) (hF z.1) (c z.1) (U z.1) z.2 - k z)
      (incrementsActualModeResidual Ahat B alpha length k) O := by
    intro z hz
    change alpha⁻¹ • U z.1 z.2 +
      incrementsModeComplexReducedOperator (F z.1) (hF z.1) (c z.1) (U z.1) z.2 - k z = _
    have hdu : DifferentiableAt ℝ (U z.1) z.2 := by
      have hd : DifferentiableAt ℝ Ujoint z :=
        (hcompat.2.1.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hp : HasFDerivAt (fun x : D => (z.1, x)) inc z.2 :=
        hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2
      have hd' : HasFDerivAt Ujoint (fderiv ℝ Ujoint z) (z.1, z.2) := hd.hasFDerivAt
      have hc : HasFDerivAt (Ujoint ∘ fun x : D => (z.1, x))
          ((fderiv ℝ Ujoint z).comp inc) z.2 := hd'.comp z.2 hp
      exact hc.differentiableAt
    rw [incrementsModeComplexReducedOperator_first_order (F z.1) (hF z.1) (c z.1)
      (U z.1) z.2 hdu]
    have hg : Ujoint =ᶠ[𝓝 z] Uhat := by
      filter_upwards [hO.mem_nhds hz] with w hw
      exact hcompat.1 hw
    have hds := (incrementsJointSpatialJets_bridge Ujoint O hO hcompat.2.1).1 z hz
    change alpha⁻¹ • Ujoint z + (B z (Ujoint z) + A z (fderiv ℝ (U z.1) z.2)) - k z = _
    rw [hds, hg.eq_of_nhds, hg.fderiv_eq]
    rfl
  intro j hj z hz
  have hevent : (fun w : X => alpha⁻¹ • U w.1 w.2 +
      incrementsModeComplexReducedOperator (F w.1) (hF w.1) (c w.1) (U w.1) w.2 - k w)
      =ᶠ[𝓝 z] incrementsActualModeResidual Ahat B alpha length k := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact he hw
  have hg := hevent.iteratedFDeriv ℝ j
  rw [hg.eq_of_nhds]
  have hn : ‖alpha‖ = tau := by simp [alpha,abs_of_pos htau]
  have ha : alpha ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact htau)
  simpa only [hn] using actual_increment_mode_residual_split_scale_jets n length O S hO hSO
    Ahat B alpha ha k hAh hB hk hAc hBc ell Mb Kb hell hell1 hM hK hAhb hBb hkb j hj z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_joint_mode_sum_split_scale_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_joint_residual_split_scale_jets
