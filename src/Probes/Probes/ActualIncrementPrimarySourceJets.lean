import Probes.ActualHomogeneousSource
import Probes.ActualIncrementJointDirectionalJets

/-! Both literal h=0 primary source channels on the original observation set.
The actual free-normal and true-B profiles produce source jets; the complex
rotation of the imaginary channel has norm one. No source budget is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actual_primary_two_channel_source_weighted_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M)
    (vfR vfI : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hvfR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O)
    (n : ℕ) (ell Mg KR KI a : ℝ) (hell : 0 ≤ ell) (hMg : 0 ≤ Mg)
    (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) (ha : 0 ≤ a)
    (hBRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hvfRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (vfR w.1 w.2 : V)) z‖ ≤ KR*a)
    (hvfIb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (vfI w.1 w.2 : V)) z‖ ≤ KI*a) :
    let k := fun z : X => actualHomogeneousSource F hF c vfR z +
      Complex.I • actualHomogeneousSource F hF c vfI z
    ContDiffOn ℝ ∞ k O ∧ ∀ r ≤ n, ∀ z ∈ S,
      ell^r * ‖iteratedFDeriv ℝ r k z‖ ≤ homogeneousSourceConstant m N n Mg (KR+KI)*a := by
  intro k
  let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
  let L := (2 : ℝ) • incrementsModeComplexInclude (m := m)
  let B : X → Fin (m+1) → V := fun z i =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)
  have channel (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
      (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O)
      (K : ℝ) (hK : 0 ≤ K)
      (hvfb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => (vf w.1 w.2 : V)) z‖ ≤ K*a) :
      ContDiffOn ℝ ∞ (actualHomogeneousSource F hF c vf) O ∧ ∀ r ≤ n, ∀ z ∈ S,
        ell^r * ‖iteratedFDeriv ℝ r (actualHomogeneousSource F hF c vf) z‖ ≤
          homogeneousSourceConstant m N n Mg K*a := by
    let v : X → V := fun z => (vf z.1 z.2 : V)
    let f : X → D := fun z => Q (B z) (v z)
    have hf : ContDiffOn ℝ ∞ f O := (Q.contDiff.comp_contDiffOn hBR).clm_apply hvf
    have he : actualHomogeneousSource F hF c vf = L ∘ f :=
      funext (actualHomogeneousSource_eq F hF c vf)
    rw [he]
    refine ⟨L.contDiff.comp_contDiffOn hf,?_⟩
    intro r hr z hz
    have hb := slow_bilinear_jet_bound_norm Q O hO B v hBR hvf r ell Mg (K*a) hell z (hSO hz)
      (fun s hs => hBRb s (hs.trans hr) z hz) (fun s hs => hvfb s (hs.trans hr) z hz)
    have hl := slow_linear_jet_bound L O hO f hf r ell
      (2^r*(‖Q‖*Mg)*(K*a)) hell z (hSO hz) hb
    apply hl.trans
    change ‖L‖*(2^r*(‖Q‖*Mg)*(K*a)) ≤ ‖L‖*2^n*‖Q‖*Mg*K*a
    calc
      _ = (‖L‖*‖Q‖*Mg*K*a)*2^r := by ring
      _ ≤ (‖L‖*‖Q‖*Mg*K*a)*2^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hr) (by positivity)
      _ = _ := by ring
  obtain ⟨hR,hRb⟩ := channel vfR hvfR KR hKR hvfRb
  obtain ⟨hI,hIb⟩ := channel vfI hvfI KI hKI hvfIb
  have hrot : ContDiffOn ℝ ∞ (fun z => Complex.I • actualHomogeneousSource F hF c vfI z) O :=
    hI.const_smul Complex.I
  refine ⟨hR.add hrot,?_⟩
  intro r hr z hz
  have hrotb : ell^r * ‖iteratedFDeriv ℝ r
      (fun z => Complex.I • actualHomogeneousSource F hF c vfI z) z‖ ≤
        homogeneousSourceConstant m N n Mg KI*a := by
    rw [iteratedFDeriv_const_smul_apply' ((hI.contDiffAt (hO.mem_nhds (hSO hz))).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞)),norm_smul,Complex.norm_I,one_mul]
    exact hIb r hr z hz
  have hh := actual_joint_slow_add_jet_bound (actualHomogeneousSource F hF c vfR)
    (fun z => Complex.I • actualHomogeneousSource F hF c vfI z) r ell _ _ hell z
    ((hR.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hrot.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) (hRb r hr z hz) hrotb
  exact hh.trans_eq (by unfold homogeneousSourceConstant; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_two_channel_source_weighted_jets
