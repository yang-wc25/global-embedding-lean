import GlobalEmbedding.Paper.IncrementsModeFullReconstruction
import GlobalEmbedding.Paper.IncrementsJointSpatialJets
import Smoothing.WeightedActualOperations

/-!
# Total parameter jets of the same inhomogeneous reconstruction

The spatial differential operator is lifted by the native spatial inclusion.
All derivatives in the estimates are genuine derivatives on Ep × D, while the
reconstruction remains the original slice formula with its actual G, J and T.
In particular parameter derivatives are not replaced by a frozen-parameter
spatial estimate. This supplies the reconstruction part of the actual secondary
mode, once the original finite solver and actual forcing have supplied their jets.

Source: main.tex, (6.2), the secondary paragraph following (6.3), and the compact
parameter clause of thm:repair. No full repair or probe target is asserted here.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

/-- The actual transverse expression, including its spatial derivative, has
total weighted jets with precisely one slow derivative loss. -/
theorem actual_joint_transverse_tensor_slow_jets
    (F : Ep → M → V) (c : Ep → D → M) (u : X → D)
    (j : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hT0 : ContDiffOn ℝ ∞
      (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hu : ContDiffOn ℝ ∞ u O)
    (ell Mg Ku : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hMg : 0 ≤ Mg)
    (hT0b : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hub : ∀ i ≤ j + 1, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u z‖ ≤ Ku) :
    let T := fun z : X => incrementsModeTransverseTensor (F z.1) (c z.1)
      (fun x => u (z.1, x)) z.2
    ContDiffOn ℝ ∞ T O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell ^ (k + 1) * ‖iteratedFDeriv ℝ k T z‖ ≤
        2 * 2 ^ k * max Mg ‖incrementsModeTransverseJet (m := m)‖ * Ku := by
  dsimp only
  let inc : D →L[ℝ] X := ContinuousLinearMap.inr ℝ Ep D
  let P : (X →L[ℝ] D) →L[ℝ] (D →L[ℝ] D) :=
    (ContinuousLinearMap.compL ℝ D X D).flip inc
  let W : (X →L[ℝ] D) →L[ℝ] Tdata :=
    (incrementsModeTransverseJet (m := m)).comp P
  let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2
  let T := fun z : X => incrementsModeTransverseTensor (F z.1) (c z.1)
    (fun x => u (z.1, x)) z.2
  let T' := fun z : X => T0 z (u z) + W (fderiv ℝ u z)
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro L
    change ‖L.comp inc‖ ≤ 1 * ‖L‖
    calc
      _ ≤ ‖L‖ * ‖inc‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by
        simpa [inc] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := Ep) (F := D))
          L.opNorm_nonneg
  have hW : ‖W‖ ≤ ‖incrementsModeTransverseJet (m := m)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left hP
        (norm_nonneg (incrementsModeTransverseJet (m := m))))
  have he : EqOn T T' O := by
    intro z hz
    dsimp only [T]
    rw [incrementsModeTransverseTensor_split,
      (incrementsJointSpatialJets_bridge u O hO hu).1 z hz]
    rfl
  have hT' : ContDiffOn ℝ ∞ T' O :=
    (hT0.clm_apply hu).add (W.contDiff.comp_contDiffOn
      (hu.fderiv_of_isOpen hO (by simp)))
  have hWb : ∀ i ≤ j, ∀ z ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun _ : X => W) z‖ ≤
        max Mg ‖incrementsModeTransverseJet (m := m)‖ := by
    intro i hi z hz
    by_cases hzero : i = 0
    · subst i
      simpa using hW.trans (le_max_right Mg _)
    · rw [iteratedFDeriv_const_of_ne hzero]
      simpa using hMg.trans (le_max_left Mg _)
  have hb := increments_first_order_scaled_jet j O S hO hSO
    (fun _ => W) T0 u contDiffOn_const hT0 hu
    ell (max Mg ‖incrementsModeTransverseJet (m := m)‖) Ku hell hell1 hWb
    (fun i hi z hz => (hT0b i hi z hz).trans (le_max_left _ _)) hub
  refine ⟨hT'.congr he, ?_⟩
  intro k hk z hz
  have hg : T =ᶠ[𝓝 z] T' := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact he hw
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb k hk z hz

/-- The original homogeneous reconstruction is jointly smooth and satisfies
the total-jet estimate, with original G/J/T0 profiles as its only geometry inputs. -/
theorem actual_joint_reconstruction_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (u : X → D)
    (j : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT0 : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hu : ContDiffOn ℝ ∞ u O)
    (ell Mg Ku : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKu : 0 ≤ Ku)
    (hGb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hT0b : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hub : ∀ i ≤ j + 1, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u z‖ ≤ Ku) :
    let R := fun z : X => incrementsModeReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x => u (z.1, x)) z.2
    ContDiffOn ℝ ∞ R O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell ^ (k + 1) * ‖iteratedFDeriv ℝ k R z‖ ≤
        (2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
          max Mg ‖incrementsModeTransverseJet (m := m)‖) * Ku := by
  dsimp only
  let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)
  let J := fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
    (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)
  let T := fun z : X => incrementsModeTransverseTensor (F z.1) (c z.1)
    (fun x => u (z.1, x)) z.2
  obtain ⟨hT, hTb⟩ := actual_joint_transverse_tensor_slow_jets F c u j O S hO hSO
    hT0 hu ell Mg Ku hell hell1 hMg hT0b hub
  have hTb' : ∀ i ≤ j, ∀ z ∈ S, ell ^ (i + 1) * ‖iteratedFDeriv ℝ i T z‖ ≤
      2 * 2 ^ j * max Mg ‖incrementsModeTransverseJet (m := m)‖ * Ku := by
    intro i hi z hz
    apply (hTb i hi z hz).trans
    gcongr
    norm_num
  have hR : ContDiffOn ℝ ∞ (fun z => G z (u z) + J z (T z)) O :=
    (hG.clm_apply hu).add (hJ.clm_apply hT)
  refine ⟨hR, ?_⟩
  intro k hk z hz
  have h0 := scaled_clm_apply O hO G u hG hu k 0 ell Mg Ku hell.le
    (fun i hi => hGb i (hi.trans hk) z hz)
    (fun i hi => by simpa using hub i (by omega) z hz) (hSO hz)
  have h0' : ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun w => G w (u w)) z‖ ≤
      2 ^ k * Mg * Ku := by
    apply le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hell.le hell1 (by omega : k ≤ k + 1)) (norm_nonneg _))
    simpa using h0
  have h1 := scaled_clm_apply O hO J T hJ hT k 1 ell Mg
    (2 * 2 ^ j * max Mg ‖incrementsModeTransverseJet (m := m)‖ * Ku) hell.le
    (fun i hi => hJb i (hi.trans hk) z hz)
    (fun i hi => hTb' i (hi.trans hk) z hz) (hSO hz)
  have hg := ((hG.clm_apply hu).contDiffAt (hO.mem_nhds (hSO hz))).of_le
    (by simp : (k : ℕ∞ω) ≤ ∞)
  have hj := ((hJ.clm_apply hT).contDiffAt (hO.mem_nhds (hSO hz))).of_le
    (by simp : (k : ℕ∞ω) ≤ ∞)
  change ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun w => G w (u w) + J w (T w)) z‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply hg hj]
  calc
    _ ≤ ell ^ (k + 1) * (‖iteratedFDeriv ℝ k (fun w => G w (u w)) z‖ +
        ‖iteratedFDeriv ℝ k (fun w => J w (T w)) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ 2 ^ k * Mg * Ku +
        2 ^ k * Mg * (2 * 2 ^ j * max Mg ‖incrementsModeTransverseJet (m := m)‖ * Ku) := by
      nlinarith [h0', h1]
    _ ≤ 2 ^ j * Mg * Ku +
        2 ^ j * Mg * (2 * 2 ^ j * max Mg ‖incrementsModeTransverseJet (m := m)‖ * Ku) := by
      gcongr <;> norm_num
    _ = _ := by rw [pow_add]; ring

/-- The actual included J times the actual transverse forcing retains every
joint direction and consumes no extra forcing derivative. -/
theorem actual_joint_forcing_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : X → Source)
    (j : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hh : ContDiffOn ℝ ∞ h O)
    (ell Mg Kh : ℝ) (hell : 0 ≤ ell) (hMg : 0 ≤ Mg) (hKh : 0 ≤ Kh)
    (hJb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hhb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h z‖ ≤ Kh) :
    let Q := fun z : X => (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2
      (incrementsModeTransverseSource (fun x => h (z.1, x)) z.2) : V)
    ContDiffOn ℝ ∞ Q O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k Q z‖ ≤
        2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh := by
  dsimp only
  let J := fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
    (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)
  let Ht := incrementsModeTransverseSourceCLM (m := m) ∘ h
  have hs : ContDiffOn ℝ ∞ Ht O :=
    incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  change ContDiffOn ℝ ∞ (fun z => J z (Ht z)) O ∧ _
  refine ⟨hJ.clm_apply hs, ?_⟩
  intro k hk z hz
  change ell ^ k * ‖iteratedFDeriv ℝ k (fun w => J w (Ht w)) z‖ ≤ _
  have hb (i : ℕ) (hi : i ≤ k) : ell ^ i * ‖iteratedFDeriv ℝ i Ht z‖ ≤
      ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh :=
    slow_linear_jet_bound incrementsModeTransverseSourceCLM O hO h hh i ell Kh
      hell z (hSO hz) (hhb i (hi.trans hk) z hz)
  have hp := scaled_clm_apply O hO J Ht hJ hs k 0 ell Mg
    (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) hell
    (fun i hi => hJb i (hi.trans hk) z hz) (fun i hi => by simpa using hb i hi) (hSO hz)
  calc
    _ ≤ 2 ^ k * Mg * (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      simpa using hp
    _ ≤ 2 ^ j * Mg * (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      gcongr
      norm_num
    _ = _ := by ring

/-- Actual zero-free inhomogeneous Z on the joint domain. The same u and h
occur in the formula and in its proven total-jet estimate. -/
theorem actual_joint_zeroFree_full_reconstruction_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (u : X → D) (h : X → Source)
    (j : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT0 : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hu : ContDiffOn ℝ ∞ u O) (hh : ContDiffOn ℝ ∞ h O)
    (ell Mg Ku Kh : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKu : 0 ≤ Ku) (hKh : 0 ≤ Kh)
    (hGb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hT0b : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hub : ∀ i ≤ j + 1, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u z‖ ≤ Ku)
    (hhb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h z‖ ≤ Kh) :
    let Z := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x => u (z.1, x)) (fun x => h (z.1, x)) (fun _ => 0) z.2
    ContDiffOn ℝ ∞ Z O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell ^ (k + 1) * ‖iteratedFDeriv ℝ k Z z‖ ≤
        (2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
          max Mg ‖incrementsModeTransverseJet (m := m)‖) * Ku +
        ell * (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) / 2 := by
  dsimp only
  let R := fun z : X => incrementsModeReconstruction (F z.1) (hF z.1) (c z.1)
    (fun x => u (z.1, x)) z.2
  let Q := fun z : X => (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2
    (incrementsModeTransverseSource (fun x => h (z.1, x)) z.2) : V)
  obtain ⟨hR, hRb⟩ := actual_joint_reconstruction_slow_jets F hF c u j O S hO hSO
    hG hJ hT0 hu ell Mg Ku hell hell1 hMg hKu hGb hJb hT0b hub
  obtain ⟨hQ, hQb⟩ := actual_joint_forcing_slow_jets F hF c h j O S hO hSO hJ hh
    ell Mg Kh hell.le hMg hKh hJb hhb
  have he : (fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x => u (z.1, x)) (fun x => h (z.1, x)) (fun _ => 0) z.2) =
        fun z => R z - (1 / 2 : ℝ) • Q z := by
    funext z
    simp only [incrementsModeFullReconstruction, Submodule.coe_zero, add_zero, R, Q]
  rw [he]
  refine ⟨hR.sub (hQ.const_smul (1 / 2 : ℝ)), ?_⟩
  intro k hk z hz
  have hr := (hR.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hq := (hQ.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [fun_iteratedFDeriv_sub_apply hr (hq.const_smul (1 / 2 : ℝ)),
    iteratedFDeriv_const_smul_apply' hq]
  calc
    _ ≤ ell ^ (k + 1) * (‖iteratedFDeriv ℝ k R z‖ +
        (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ k Q z‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using norm_sub_le (iteratedFDeriv ℝ k R z) ((1 / 2 : ℝ) • iteratedFDeriv ℝ k Q z)
    _ = ell ^ (k + 1) * ‖iteratedFDeriv ℝ k R z‖ +
        ell * (ell ^ k * ‖iteratedFDeriv ℝ k Q z‖) / 2 := by rw [pow_succ]; ring
    _ ≤ _ := add_le_add (hRb k hk z hz)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hQb k hk z hz) hell.le)
        (by norm_num))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_transverse_tensor_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_joint_reconstruction_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_joint_forcing_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_joint_zeroFree_full_reconstruction_slow_jets
