import NormalPolar.JointSecondaryCarrierPerturbation

/-! A common hierarchy for the actual original phases on their closed
carriers. All native charts, perturbation radii and bounds are manufactured
from the original smooth immersion and original individual Good data.
Weights are chosen before every contraction or oscillation scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

private theorem originalPhase_power_ratio {A : ℝ} (hA : 1 < A) {i j : ℕ} (hij : i < j) :
    0 ≤ (A ^ (j-i))⁻¹ ∧ (A ^ (j-i))⁻¹ ≤ A⁻¹ ∧
      A^j * (A^(j-i))⁻¹ = A^i := by
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hp : A ≤ A^(j-i) := by
    simpa only [pow_one] using pow_le_pow_right₀ hA.le (show 1 ≤ j-i by omega)
  have hj : A^j = A^i * A^(j-i) := by
    rw [← pow_add,Nat.add_sub_of_le hij.le]
  refine ⟨inv_nonneg.mpr (pow_nonneg hA0.le _),
    (inv_le_inv₀ (pow_pos hA0 _) hA0).mpr hp,?_⟩
  rw [hj,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hA0.ne'),mul_one]

variable {m N : ℕ} {M Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [Fintype Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

private theorem originalPhase_ordered_good
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F) (x : M)
    (xi eta : TangentSpace IM x →L[ℝ] ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hpert : ∀ t : ℝ, |t| < epsilon → GoodCovector F hF x (eta + t • xi))
    {i j : ℕ} (hij : i < j) :
    let A := hierarchicalGoodWeight epsilon 1
    GoodCovector F hF x (A^j • eta + A^i • xi) ∧
      GoodCovector F hF x (A^j • eta - A^i • xi) := by
  let A := hierarchicalGoodWeight epsilon 1
  have hA : 1 < A := hierarchicalGoodWeight_gt_one he zero_le_one
  have hA0 : A ≠ 0 := (zero_lt_one.trans hA).ne'
  let t : ℝ := (A^(j-i))⁻¹
  obtain ⟨ht0,htA,htpow⟩ := originalPhase_power_ratio hA hij
  have ht : t < epsilon := htA.trans_lt
    (by simpa only [mul_one] using hierarchicalGoodWeight_small_ratio he (show (0:ℝ) ≤ 1 by norm_num))
  have ht0' : 0 ≤ t := ht0
  have htpow' : A^j * t = A^i := htpow
  have hp := hpert t (by rw [abs_of_nonneg ht0']; exact ht)
  have hm := hpert (-t) (by rw [abs_neg,abs_of_nonneg ht0']; exact ht)
  have hplus : A^j • (eta + t • xi) = A^j • eta + A^i • xi := by
    rw [smul_add,smul_smul,htpow]
  have hminus : A^j • (eta + (-t) • xi) = A^j • eta - A^i • xi := by
    ext v
    change A^j * (eta v + (-t) * xi v) = A^j * eta v - A^i * xi v
    calc
      _ = A^j * eta v - (A^j*t) * xi v := by ring
      _ = _ := by rw [htpow']
  constructor
  · rw [← hplus]
    exact (jointSecondary_original_good_smul_iff F hF x _ _ (pow_ne_zero _ hA0)).mpr hp
  · rw [← hminus]
    exact (jointSecondary_original_good_smul_iff F hF x _ _ (pow_ne_zero _ hA0)).mpr hm

theorem jointSecondary_original_compact_phase_weights
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (phase : Label → M → ℝ) (K O : Label → Set M)
    (hK : ∀ l, IsClosed (K l)) (hO : ∀ l, IsOpen (O l)) (hKO : ∀ l, K l ⊆ O l)
    (hphase : ∀ l, ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (phase l) (O l))
    (hgood : ∀ l x, x ∈ K l → GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) (phase l) x))
    (label : Label → ℕ) :
    ∃ A : ℝ, 1 < A ∧
      (∀ l x, x ∈ K l → GoodCovector F hF x
        (A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x)) ∧
      (∀ l x, x ∈ K l → GoodCovector F hF x
        ((2:ℝ) • (A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x))) ∧
      ∀ l l' x, x ∈ K l ∩ K l' → label l ≠ label l' →
        GoodCovector F hF x
          (A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x +
            A^(label l') • jointSecondaryPhaseCovector (m := m) (phase l') x) ∧
        GoodCovector F hF x
          (A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x -
            A^(label l') • jointSecondaryPhaseCovector (m := m) (phase l') x) := by
  choose epsilon heps hpert using fun ij : Label × Label =>
    jointSecondary_compact_carrier_phase_perturbation F hF hImm (phase ij.1) (phase ij.2)
      (K ij.1 ∩ K ij.2) (O ij.1 ∩ O ij.2) ((hK ij.1).inter (hK ij.2))
      ((hO ij.1).inter (hO ij.2)) (fun _ hx => ⟨hKO ij.1 hx.1,hKO ij.2 hx.2⟩)
      ((hphase ij.1).mono inter_subset_left) ((hphase ij.2).mono inter_subset_right)
      (fun x hx => hgood ij.1 x hx.1)
  obtain ⟨eps,heps0,hle⟩ := finite_positive_common_lower_bound epsilon heps
  let A := hierarchicalGoodWeight eps 1
  have hA : 1 < A := hierarchicalGoodWeight_gt_one heps0 zero_le_one
  have hA0 : A ≠ 0 := (zero_lt_one.trans hA).ne'
  have hprimary (l : Label) (x : M) (hx : x ∈ K l) :
      GoodCovector F hF x (A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x) := by
    apply (jointSecondary_original_good_smul_iff F hF x _ _ (pow_ne_zero _ hA0)).mpr
    rw [jointSecondaryPhaseCovector_eq]
    exact hgood l x hx
  refine ⟨A,hA,hprimary,?_,?_⟩
  · intro l x hx
    exact (jointSecondary_original_good_smul_iff F hF x _ (2:ℝ) (by norm_num)).mpr
      (hprimary l x hx)
  · intro l l' x hx hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hb := originalPhase_ordered_good (m := m) F hF x
        (jointSecondaryPhaseCovector (m := m) (phase l) x) (jointSecondaryPhaseCovector (m := m) (phase l') x)
        heps0 (fun t ht => hpert (l',l) t (ht.trans_le (hle _)) x ⟨hx.2,hx.1⟩) hlt
      refine ⟨by simpa only [add_comm] using hb.1,?_⟩
      have hn := (jointSecondary_original_good_smul_iff F hF x
        (A^(label l') • jointSecondaryPhaseCovector (m := m) (phase l') x -
          A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x) (-1:ℝ) (by norm_num)).mpr hb.2
      have heq : (-1:ℝ) • (A^(label l') • jointSecondaryPhaseCovector (m := m) (phase l') x -
          A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x) =
          A^(label l) • jointSecondaryPhaseCovector (m := m) (phase l) x -
            A^(label l') • jointSecondaryPhaseCovector (m := m) (phase l') x := by
        ext v
        simp
      rwa [heq] at hn
    · exact originalPhase_ordered_good (m := m) F hF x
        (jointSecondaryPhaseCovector (m := m) (phase l') x) (jointSecondaryPhaseCovector (m := m) (phase l) x)
        heps0 (fun t ht => hpert (l,l') t (ht.trans_le (hle _)) x hx) hgt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_compact_phase_weights
