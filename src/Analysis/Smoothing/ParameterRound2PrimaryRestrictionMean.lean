import Smoothing.ParameterRound2PrimaryRestrictionReconstruction

/-! Restricting the actual subordinate charts preserves the SAME primary
wave, native spatial coefficients, Gram mean and mean error on the proved
joint neighborhood. The finite construction has not been replaced by a
chosen extension or a different zero-mode operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_actual_spatialDerivative_eqOn
    (u v : Ep × M → V) (G : Set (Ep × M)) (hG : IsOpen G) (he : EqOn u v G) :
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

theorem parameterRound2_restrictPrimary_amplitude
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) :
    EqOn (incrementsGlobalPrimaryAmplitude F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν)
      (incrementsGlobalPrimaryAmplitude F hF g input length tau realChannel ν) G := by
  intro z hz
  exact Finset.sum_congr rfl fun β hβ =>
    parameterRound2_restrictPrimary_extension F hF g G hG input length tau realChannel ν β hz

theorem parameterRound2_restrictPrimary_wave
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    EqOn (incrementsGlobalPrimaryWave F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau) (incrementsGlobalPrimaryWave F hF g input length tau) G := by
  intro z hz
  apply Finset.sum_congr rfl
  intro ν hν
  rw [parameterRound2_restrictPrimary_amplitude F hF g G hG input length tau true ν hz,
    parameterRound2_restrictPrimary_amplitude F hF g G hG input length tau false ν hz]
  rfl

theorem parameterRound2_restrictPrimary_coefficient
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (z : Ep × M) (hz : z ∈ G) :
    incrementsGlobalPrimaryCoefficient F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν z =
      incrementsGlobalPrimaryCoefficient F hF g input length tau realChannel ν z := by
  have hslow := parameterRound2_actual_spatialDerivative_eqOn (I := I) _ _ G hG
    (parameterRound2_restrictPrimary_amplitude F hF g G hG input length tau realChannel ν) z hz
  have hother := parameterRound2_restrictPrimary_amplitude F hF g G hG input length tau (!realChannel) ν hz
  dsimp only [incrementsGlobalPrimaryCoefficient]
  rw [hslow,hother]
  rfl

theorem parameterRound2_restrictPrimary_mean
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    ∀ z ∈ G, incrementsGlobalPrimaryMean F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau z.1 z.2 = incrementsGlobalPrimaryMean F hF g input length tau z.1 z.2 := by
  intro z hz
  unfold incrementsGlobalPrimaryMean
  congr 1
  apply Finset.sum_congr rfl
  intro ν hν
  rw [parameterRound2_restrictPrimary_coefficient F hF g G hG input length tau true ν z hz,
    parameterRound2_restrictPrimary_coefficient F hF g G hG input length tau false ν z hz]

theorem parameterRound2_restrictPrimary_meanError
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) :
    ∀ z ∈ G, incrementsGlobalPrimaryMeanError F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau z.1 z.2 = incrementsGlobalPrimaryMeanError F hF g input length tau z.1 z.2 := by
  intro z hz
  exact congrArg (fun A => A-input z.1 z.2)
    (parameterRound2_restrictPrimary_mean F hF g G hG input length tau z hz)

#print axioms parameterRound2_restrictPrimary_wave
#print axioms parameterRound2_restrictPrimary_mean
#print axioms parameterRound2_restrictPrimary_meanError
end GlobalEmbedding.Continuation
