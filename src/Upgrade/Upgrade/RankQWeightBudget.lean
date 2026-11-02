import Upgrade.RankQFixedWeightSimulation

/-!
A fixed positive simulation constant is chosen after the provider's weight
list is known. It depends on those two finite weight lists alone, and never
on the scale, parameter, source point or fast angles. This is packaging of
the already proved finite coefficient bound, not a new principal algebra.
-/

noncomputable section
namespace GlobalEmbedding.Upgrade

variable {ι : Type*} [Fintype ι]

def rankQWeightSimulationBound (lambda mu : ι → Fin 2 → ℝ) : ℝ :=
  Classical.choose (exists_fixed_weight_simulation_bound lambda mu)

theorem rankQWeightSimulationBound_pos (lambda mu : ι → Fin 2 → ℝ) :
    0 < rankQWeightSimulationBound lambda mu :=
  (Classical.choose_spec (exists_fixed_weight_simulation_bound lambda mu)).1

theorem rankQWeightSimulationBound_le (lambda mu : ι → Fin 2 → ℝ) (i : ι) (j : Fin 2) :
    2 * ‖rankQWeightSimulationCoeff lambda mu i j‖ ≤ rankQWeightSimulationBound lambda mu :=
  (Classical.choose_spec (exists_fixed_weight_simulation_bound lambda mu)).2 i j

end GlobalEmbedding.Upgrade
