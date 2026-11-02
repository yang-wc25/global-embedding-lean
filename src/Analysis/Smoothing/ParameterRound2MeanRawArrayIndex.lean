import Smoothing.ParameterRound2MeanRawProfilesIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-! Uniform all-ordered-component raw mean bound. The only finite sum in
the chosen constant is over the fixed source dimension, never over charts. -/

theorem parameterRound2_actual_raw_globalMean_array_uniform_index
    (n length j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ k, 0 ≤ T k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta),
    let meanA := fun z (a : Fin (m+1) × Fin (m+1)) =>
      parameterRound2_globalObservedMeanCoefficient F hF g input length tau e z a.1 a.2
    let meanB := fun z (a : Fin (m+1) × Fin (m+1)) =>
      parameterRound2_globalObservedMeanCoefficient F hF g inputbar length tau e z a.1 a.2
    (∀ a, ContDiffOn ℝ ∞ (fun z => meanA z a) O ∧ ContDiffOn ℝ ∞ (fun z => meanB z a) O) ∧
    (∀ a k, k ≤ j → ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanA w a) z‖ ≤ K*(tau/ell)) ∧
    (∀ a k, k ≤ j → ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanB w a) z‖ ≤ K*(tau/ell)) ∧
    (∀ a k, k ≤ j → ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanA w a-meanB w a) z‖ ≤ K*(tau/ell)*Delta) := by
  have hall (a : Fin (m+1) × Fin (m+1)) :=
    parameterRound2_actual_raw_globalMean_uniform_index
      (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
      n length j Rsub Lprimary a.1 a.2 horder c Bnd Mg hc hBnd hMg T hTnonneg
  choose K hK hbound using hall
  let C := ∑ a, K a
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => hK a)
  have hKC (a) : K a ≤ C := Finset.single_le_sum (fun b _ => hK b) (Finset.mem_univ a)
  refine ⟨C,hC,?_⟩
  intro Λ Β _ _ F hF g input inputbar W primary e O S tau ell Delta data meanA meanB
  have hh (a) := hbound a F hF g input inputbar W primary e O S tau ell Delta data
  have heps : 0 ≤ tau/ell := div_nonneg data.htau.le (data.htau.trans_le data.htaul).le
  refine ⟨fun a => (hh a).1,?_,?_,?_⟩
  · intro a k hk z hz
    exact ((hh a).2.1 k hk z hz).trans (mul_le_mul_of_nonneg_right (hKC a) heps)
  · intro a k hk z hz
    exact ((hh a).2.2.1 k hk z hz).trans (mul_le_mul_of_nonneg_right (hKC a) heps)
  · intro a k hk z hz
    exact ((hh a).2.2.2 k hk z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hKC a) heps) data.hDelta)

#print axioms parameterRound2_actual_raw_globalMean_array_uniform_index
end GlobalEmbedding.Continuation
