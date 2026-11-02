import NormalPolar.JointMixedGroupedDifferenceNorm
import NormalPolar.JointBackgroundGroupedOriginalGerm

/-! One literal normalized grouped forcing family is constructed on the
original tensor germ space. Its full all-order quadratic two-parameter
difference estimate is produced from primitive profiles. The representative
is fixed before any difference or derivative; normalization occurs once. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M P : Type*} {m N d p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
variable {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem jointMixed_grouped_original_forcing_pair_from_raw
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hCompact : ∀ idx, IsCompact (Samples idx))
    (hOrig : ∀ idx, Samples idx ⊆ incrementsOriginalDifferentiation A B idx)
    (n : ℕ → ℕ) (length : ℕ) (horder : ∀ j, j+2+length ≤ n j)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j k, 0 ≤ T j k)
    (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℕ → ℝ)
    (hMg : ∀ j, 0 ≤ Mg j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M)
    (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) →
      normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (phase : Fin r → P × M → ℝ)
    (tau ell delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hdelta : 0 < delta)
    (Omega : ℕ → Fin A.count × Fin count → Set X) (hOmega : ∀ j idx, IsOpen (Omega j idx))
    (hOmegaSub : ∀ j idx, Omega j idx ⊆ (B idx.2).target ×ˢ (A.chart idx.1).target)
    (hSamples : ∀ j idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega j idx)
    (profiles : ∀ j idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
      (B idx.2) (A.chart idx.1) (Omega j idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
      (n j) j ell (Mg j) (Bchi j) (Bnu j) (Mphase j) (T j)) :
    let C := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p (n j) length j (T j) weight
        (Mg j) (Bchi j) (Bnu j) (Mphase j) 1
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let mean := fun u b x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u b x
    let pj := parameterRound2_originalTensorGermSeminorm A B Samples univ hCompact hOrig ell
    ∃ Pforce : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace A B Samples univ,
      (∀ u, (Pforce u).val = (delta^2)⁻¹ • mean u) ∧
      (∀ j u, pj j (Pforce u) ≤ C j*‖u‖^2) ∧
      (∀ j u v, pj j (Pforce u-Pforce v) ≤ C j*(‖u‖+‖v‖)*‖u-v‖) := by
  intro C vf mean pj
  have hub (u : Fin p → ℝ) (j : ℕ) (idx : Fin A.count × Fin count)
      (k : ℕ) (_hk : k ≤ j) (z : X) (_hz : parameterTensorModelEquiv (m+1) d z ∈ Samples idx) :
      ell^k*‖iteratedFDeriv ℝ k (fun _ : X => u) z‖ ≤ ‖u‖ := by
    cases k with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,one_mul]; exact le_rfl
    | succ k => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,mul_zero] using norm_nonneg u
  have hraw (j : ℕ) (u : Fin p → ℝ) := jointBackground_grouped_original_mean_raw_germ
    label F hF c chi nu a ha (n j) length j (horder j) tau ell delta weight
    (Mg j) (Bchi j) (Bnu j) (Mphase j) ‖u‖ htau htaul hell1 (hMg j) hdelta.le
    (hBchi j) (hBnu j) (hMphase j) (norm_nonneg u) A B hA Samples
    (Omega j) (hOmega j) (hOmegaSub j) (hSamples j) (T j) (hT j) phase (profiles j)
    (fun _ => u) (fun _ => contDiffOn_const) (hub u j) univ hCompact hOrig hdelta.ne'
  have hmem (u : Fin p → ℝ) : mean u ∈ parameterRound2_originalTensorGermSpace A B Samples univ := by
    obtain ⟨g,hg,_,_⟩ := hraw 0 u
    change g.val = mean u at hg
    rw [← hg]
    exact g.property
  let probe := fun u : Fin p → ℝ => (⟨mean u,hmem u⟩ : parameterRound2_originalTensorGermSpace A B Samples univ)
  let Pforce := fun u : Fin p → ℝ => (delta^2)⁻¹ • probe u
  refine ⟨Pforce,fun _ => rfl,?_,?_⟩
  · intro j u
    obtain ⟨other,hother,_,hb⟩ := hraw j u
    have he : other = probe u := Subtype.ext hother
    rw [he] at hb
    exact hb.trans_eq (by
      rw [jointGroupedPrescribedMeanUniformCost_amplitude_sq]
      dsimp only [C]
      ring)
  · intro j u v
    have hn := jointMixed_grouped_original_mean_difference_raw_norm label F hF c chi nu a ha
      (n j) length j (horder j) tau ell delta weight (Mg j) (Bchi j) (Bnu j) (Mphase j)
      htau htaul hell1 (hMg j) hdelta.le (hBchi j) (hBnu j) (hMphase j) A B hA Samples
      (Omega j) (hOmega j) (hOmegaSub j) (hSamples j) (T j) (hT j) phase (profiles j) u v
    have hb : pj j (probe u-probe v) ≤ C j*delta^2*(‖u‖+‖v‖)*‖u-v‖ := hn.2.2
    change pj j ((delta^2)⁻¹ • probe u-(delta^2)⁻¹ • probe v) ≤ _
    rw [← smul_sub,map_smul_eq_mul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg delta))]
    calc
      _ ≤ (delta^2)⁻¹*(C j*delta^2*(‖u‖+‖v‖)*‖u-v‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sq_nonneg delta))
      _ = _ := by
        have hd : delta ≠ 0 := hdelta.ne'
        field_simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_grouped_original_forcing_pair_from_raw
