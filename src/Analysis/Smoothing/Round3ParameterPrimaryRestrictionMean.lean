import Smoothing.Round3ParameterPrimaryRestrictionReconstruction

/-! Restricting the actual subordinate charts preserves the SAME primary
wave, native spatial coefficients, Gram mean and mean error on the proved
joint neighborhood. The finite construction has not been replaced by a
chosen extension or a different zero-mode operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem round3Parameter_actual_spatialDerivative_eqOn
    (u v : P × M → V) (G : Set (P × M)) (hG : IsOpen G) (he : EqOn u v G) :
    ∀ z ∈ G, incrementsGlobalSpatialDerivative (I := I) u z =
      incrementsGlobalSpatialDerivative (I := I) v z := by
  intro z hz
  have hh : (fun x => u (z.1,x)) =ᶠ[𝓝 z.2] (fun x => v (z.1,x)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
      (hG.mem_nhds hz)] with x hx
    exact he hx
  have hm := hh.mfderiv_eq (I := I) (I' := 𝓘(ℝ,V))
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg (fun L => L w) hm

theorem round3Parameter_restrictPrimary_amplitude
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) :
    EqOn (round3ParameterPrimaryAmplitude F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν)
      (round3ParameterPrimaryAmplitude F hF g input length tau realChannel ν) G := by
  intro z hz
  exact Finset.sum_congr rfl fun β hβ =>
    round3Parameter_restrictPrimary_extension F hF g G hG input length tau realChannel ν β hz

theorem round3Parameter_restrictPrimary_wave
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    EqOn (round3ParameterPrimaryWave F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau) (round3ParameterPrimaryWave F hF g input length tau) G := by
  intro z hz
  apply Finset.sum_congr rfl
  intro ν hν
  rw [round3Parameter_restrictPrimary_amplitude F hF g G hG input length tau true ν hz,
    round3Parameter_restrictPrimary_amplitude F hF g G hG input length tau false ν hz]
  rfl

theorem round3Parameter_restrictPrimary_coefficient
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (z : P × M) (hz : z ∈ G) :
    round3ParameterPrimaryCoefficient F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν z =
      round3ParameterPrimaryCoefficient F hF g input length tau realChannel ν z := by
  have hslow := round3Parameter_actual_spatialDerivative_eqOn (I := I) _ _ G hG
    (round3Parameter_restrictPrimary_amplitude F hF g G hG input length tau realChannel ν) z hz
  have hother := round3Parameter_restrictPrimary_amplitude F hF g G hG input length tau (!realChannel) ν hz
  dsimp only [round3ParameterPrimaryCoefficient]
  rw [hslow,hother]
  rfl

theorem round3Parameter_restrictPrimary_mean
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    ∀ z ∈ G, round3ParameterPrimaryMean F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau z.1 z.2 = round3ParameterPrimaryMean F hF g input length tau z.1 z.2 := by
  intro z hz
  unfold round3ParameterPrimaryMean
  congr 1
  apply Finset.sum_congr rfl
  intro ν hν
  rw [round3Parameter_restrictPrimary_coefficient F hF g G hG input length tau true ν z hz,
    round3Parameter_restrictPrimary_coefficient F hF g G hG input length tau false ν z hz]

theorem round3Parameter_restrictPrimary_meanError
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    ∀ z ∈ G, round3ParameterPrimaryMeanError F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau z.1 z.2 = round3ParameterPrimaryMeanError F hF g input length tau z.1 z.2 := by
  intro z hz
  exact congrArg (fun A => A-input z.1 z.2)
    (round3Parameter_restrictPrimary_mean F hF g G hG input length tau z hz)

#print axioms round3Parameter_restrictPrimary_wave
#print axioms round3Parameter_restrictPrimary_mean
#print axioms round3Parameter_restrictPrimary_meanError
end GlobalEmbedding.Continuation
