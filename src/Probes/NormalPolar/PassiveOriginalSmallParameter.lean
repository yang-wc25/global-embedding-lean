import NormalPolar.PassiveOriginalSmallBuffer
import NormalPolar.ParameterDisplacementGlobalParameterProfiles

/-! A genuinely small smooth parameter on all of P, selected at input
initialization. Its actual zero-order profile is the prescribed amplitude,
while every positive-order profile comes from the same fixed cutoff on the
same original compact Q samples. The original ball is the one associated
with this legal initial buffer and is retained in full thereafter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar

variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

def passiveOriginalAmplitudeAtlas (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude) : BufferedAtlas P (EuclideanSpace ℝ (Fin d)) :=
  passiveOriginalSmallBuffer B
    (amplitude/(‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (div_pos ha (by positivity))

def passiveOriginalSmallParameter (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude) (b : Fin B.count) (p₀ : P) : P → Fin d → ℝ :=
  actualRepairGlobalParameter (tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha)) b p₀

theorem passiveOriginalSmallParameter_bound
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude) (b : Fin B.count) (p₀ p : P) :
    ‖passiveOriginalSmallParameter B amplitude ha b p₀ p‖ ≤ amplitude := by
  let c := ‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  have ha' : 0 ≤ amplitude/(c+1) := le_of_lt (div_pos ha (by positivity))
  calc
    _ ≤ c*(passiveOriginalAmplitudeAtlas B amplitude ha).buffer :=
      actualRepairGlobalParameter_norm_le _ b p₀ p
    _ ≤ c*(amplitude/(c+1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc
    _ ≤ (c+1)*(amplitude/(c+1)) := mul_le_mul_of_nonneg_right (by linarith) ha'
    _ = amplitude := by field_simp

theorem passiveOriginalSmallParameter_local_identity
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude) (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : Fin d → ℝ)
    (hv : ‖v‖ < actualRepairParameterRadius
      (tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha))) :
    passiveOriginalSmallParameter B amplitude ha b p₀
      (actualRepairParameterMap (tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha)) b p₀ v) = v :=
  actualRepairGlobalParameter_local_identity _ b p₀ hp₀ v hv

variable {Es : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es]

/-- The same fixed function supplies all orders, with Ku(0) exactly the
small actual amplitude. Constants precede every slow derivative scale. -/
theorem passiveOriginalSmallParameter_joint_profiles
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ i, IsCompact (Q i)) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (amplitude : ℝ) (ha : 0 < amplitude) (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) 𝓘(ℝ,Fin d → ℝ) ∞
      (passiveOriginalSmallParameter B amplitude ha b p₀) ∧
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
      (∀ i, ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin d) × Es =>
        passiveOriginalSmallParameter B amplitude ha b p₀ ((B.chart i).symm z.1))
        (Prod.fst ⁻¹' (B.chart i).target)) ∧
      ∀ j ell, 0 ≤ ell → ell ≤ 1 → ∀ k, k ≤ j → ∀ i z, z.1 ∈ Q i →
        ell^k*‖iteratedFDeriv ℝ k (fun y : EuclideanSpace ℝ (Fin d) × Es =>
          passiveOriginalSmallParameter B amplitude ha b p₀ ((B.chart i).symm y.1)) z‖ ≤ Ku j := by
  let B' := tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha)
  have hB' : ∀ i, B'.chart i ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P := hB.chart_mem
  obtain ⟨K,hK,hs,hjets⟩ := actualRepairGlobalParameter_joint_fixed_profiles (Es := Es)
    B' hB' Q hQ hQT b p₀ hp₀
  refine ⟨actualRepairGlobalParameter_smooth B' hB' b p₀ hp₀,
    (fun j => if j = 0 then amplitude else K j),?_,by simp,hs,?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact ha.le
    · exact hK j
  · intro j ell hell hell1 k hk i z hz
    by_cases hj : j = 0
    · subst j
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa only [ite_true,pow_zero,one_mul,norm_iteratedFDeriv_zero] using
        passiveOriginalSmallParameter_bound B amplitude ha b p₀ ((B.chart i).symm z.1)
    · simp only [ite_eq_right hj]
      change ell^k*‖iteratedFDeriv ℝ k (fun y : EuclideanSpace ℝ (Fin d) × Es =>
        actualRepairGlobalParameter B' b p₀ ((B'.chart i).symm y.1)) z‖ ≤ K j
      exact hjets j ell hell hell1 k hk i z hz

/-- An actual positive amplitude selected from the primitive zero-order
source cost and reserve, before the new buffer, any derivative scale, or
any oscillation is chosen. -/
def passiveOriginalReserveAmplitude (sourceCost rho : ℝ) : ℝ :=
  Real.sqrt (rho/(4*(max 0 sourceCost+1)))

theorem passiveOriginalReserveAmplitude_pos (sourceCost rho : ℝ) (hrho : 0 < rho) :
    0 < passiveOriginalReserveAmplitude sourceCost rho := by
  apply Real.sqrt_pos.mpr
  exact div_pos hrho (mul_pos (by norm_num) (by positivity))

theorem passiveOriginalReserveAmplitude_small (sourceCost rho : ℝ) (hrho : 0 < rho) :
    sourceCost*(passiveOriginalReserveAmplitude sourceCost rho)^2 ≤ rho/4 := by
  have hc : 0 < max 0 sourceCost+1 := by positivity
  have hnonneg : 0 ≤ rho/(4*(max 0 sourceCost+1)) :=
    (div_pos hrho (mul_pos (by norm_num) hc)).le
  rw [passiveOriginalReserveAmplitude,Real.sq_sqrt hnonneg]
  calc
    _ ≤ (max 0 sourceCost+1)*(rho/(4*(max 0 sourceCost+1))) :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_right 0 sourceCost]) hnonneg
    _ = rho/4 := by field_simp

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_joint_profiles
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_local_identity
#print axioms GlobalEmbedding.Continuation.passiveOriginalReserveAmplitude_small
