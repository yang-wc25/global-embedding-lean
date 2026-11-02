import Probes.ActualRepairGermNormAlgebra
import Smoothing.ParameterRound2MeanResidualScaling

/-! Original weighted norms for the actual next-step pair. Positive inherited
orders gain the true ratio tau/t. The displacement's base-two norm loses two
powers of tau, with its higher-order norm taken from the SAME map. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {ι : Type*} [Fintype ι] {a q : ℕ}

theorem actual_paper_weighted_add_germs
    (base j : ℕ) {tau : ℝ} (htau : 0 < tau)
    (f g : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (f i) U)
    (hg : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (g i) U)
    (hff : paperAtlasWeighted base j tau f O S ≠ ⊤)
    (hgf : paperAtlasWeighted base j tau g O S ≠ ⊤) :
    paperAtlasWeighted base j tau (fun i x => f i x+g i x) O S ≠ ⊤ ∧
    (paperAtlasWeighted base j tau (fun i x => f i x+g i x) O S).toReal ≤
      (paperAtlasWeighted base j tau f O S).toReal+(paperAtlasWeighted base j tau g O S).toReal := by
  choose Of hOf hSf hfs using hf
  choose Og hOg hSg hgs using hg
  let U := fun i => O i ∩ (Of i ∩ Og i)
  have hU (i) : IsOpen (U i) := (hO i).inter ((hOf i).inter (hOg i))
  have hSU : ∀ i, S i ⊆ U i := fun i x hx => ⟨hSO i hx,hSf i hx,hSg i hx⟩
  have hUO : ∀ i, U i ⊆ O i := fun _ => inter_subset_left
  have he (u : ι → (Fin a → ℝ) → Fin q → ℝ) :=
    actual_paperAtlasWeighted_open_restrict base j tau u O U S hO hU hUO hSU
  have hft := parameterRound2_topOrder_finite_of_weighted base j htau f U S ((he f) ▸ hff)
  have hgt := parameterRound2_topOrder_finite_of_weighted base j htau g U S ((he g) ▸ hgf)
  have hh := parameterRound2_paperAtlasWeighted_add_le base j tau f g U S hU hSU
    (fun i => (hfs i).mono (fun _ hx => hx.2.1))
    (fun i => (hgs i).mono (fun _ hx => hx.2.2)) hft hgt
  rw [← he,← he,← he] at hh
  have hfin := ENNReal.add_ne_top.mpr ⟨hff,hgf⟩
  refine ⟨ne_top_of_le_ne_top hfin hh,?_⟩
  exact (ENNReal.toReal_mono hfin hh).trans_eq (ENNReal.toReal_add hff hgf)

theorem actual_paper_weighted_base_shift
    (base j : ℕ) {tau : ℝ} (htau : 0 < tau)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasWeighted 0 (j+base) tau f O S ≠ ⊤) :
    paperAtlasWeighted base j tau f O S ≠ ⊤ ∧
      (paperAtlasWeighted base j tau f O S).toReal ≤
        (j+1)*(paperAtlasWeighted 0 (j+base) tau f O S).toReal/tau^base := by
  have htop : paperAtlasCj (j+base) f O S ≠ ⊤ := by
    simpa only [Nat.add_zero] using parameterRound2_topOrder_finite_of_weighted 0 (j+base) htau f O S hfinite
  have hshift := parameterRound2_paperAtlasWeighted_finite_of_topOrder base j tau f O S htop
  refine ⟨hshift,?_⟩
  rw [paperAtlasWeighted_toReal base j tau htau.le f O S hshift]
  calc
    _ ≤ ∑ _i ∈ Finset.range (j+1), (paperAtlasWeighted 0 (j+base) tau f O S).toReal/tau^base := by
      apply Finset.sum_le_sum
      intro i hi
      have hindex : i+base < j+base+1 := by have := Finset.mem_range.mp hi; omega
      have hle : ENNReal.ofReal tau^(i+base)*paperAtlasCj (i+base) f O S ≤
          paperAtlasWeighted 0 (j+base) tau f O S := by
        simpa only [paperAtlasWeighted,Nat.add_zero] using Finset.single_le_sum (fun r hr => (zero_le : (0 : ℝ≥0∞) ≤
          ENNReal.ofReal tau^r*paperAtlasCj (r+0) f O S)) (Finset.mem_range.mpr hindex)
      have hh := ENNReal.toReal_mono hfinite hle
      rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal htau.le] at hh
      apply (le_div_iff₀ (pow_pos htau base)).mpr
      calc
        _ = tau^(i+base)*(paperAtlasCj (i+base) f O S).toReal := by rw [pow_add]; ring
        _ ≤ _ := hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; ring

theorem actual_paper_weighted_inherited_scale
    (base j : ℕ) {tau t : ℝ} (htau : 0 ≤ tau) (ht : 0 < t)
    (htaul : tau ≤ t)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasWeighted base j t f O S ≠ ⊤) :
    paperAtlasWeighted base j tau f O S ≠ ⊤ ∧
      (paperAtlasWeighted base j tau f O S).toReal ≤ (paperAtlasCj base f O S).toReal+
        (tau/t)*(paperAtlasWeighted base j t f O S).toReal := by
  have hsmall := ne_top_of_le_ne_top hfinite
    (parameterRound2_paperAtlasWeighted_mono_scale base j tau t htaul f O S)
  refine ⟨hsmall,?_⟩
  rw [paperAtlasWeighted_toReal base j tau htau f O S hsmall,
    paperAtlasWeighted_toReal base j t ht.le f O S hfinite,
    Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [pow_zero,zero_add,one_mul]
  have hh : (∑ i ∈ Finset.range j, tau^(i+1)*(paperAtlasCj (i+1+base) f O S).toReal) ≤
      (tau/t)*(∑ i ∈ Finset.range j, t^(i+1)*(paperAtlasCj (i+1+base) f O S).toReal) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp : tau^(i+1) ≤ (tau/t)*t^(i+1) := by
      calc
        _ = tau*tau^i := by rw [pow_succ]; ring
        _ ≤ tau*t^i := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htau htaul i) htau
        _ = _ := by rw [pow_succ]; field_simp
    exact (mul_le_mul_of_nonneg_right hp ENNReal.toReal_nonneg).trans_eq (by ring)
  have hbase := ENNReal.toReal_nonneg (a := paperAtlasCj base f O S)
  have hratio : 0 ≤ tau/t := div_nonneg htau ht.le
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_paper_weighted_add_germs
#print axioms GlobalEmbedding.Continuation.actual_paper_weighted_base_shift
#print axioms GlobalEmbedding.Continuation.actual_paper_weighted_inherited_scale
