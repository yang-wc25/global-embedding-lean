import Probes.Round3ParameterOriginalDomain
import Probes.Round3ParameterJointConclusion
import Probes.Round3RepairActualDisplacement
import Smoothing.ParameterRound2RepairIdentity

/-! The whole-parameter repair caller consumes the same actual increment.
When the original parameter set is all P, its canonical domain is all P×M;
the next map is therefore globally jointly smooth.  This is the exact
regularity required for the next actual smoothing stage.  The growing-order
budget is the original nonweighted MAX of that very same U. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local instance round3ParameterWholeRepairChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3ParameterWholeRepairIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round3Parameter_whole_repair_next_map_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hK : Data.parameterSet = univ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ))
    (oldMap U : P × M → V)
    (hOld : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ oldMap)
    (q : ℕ) (delta tau ell : ℝ) (Cmap Cmetric : ℕ → ℝ)
    (hout : Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart S
      (round3ParameterOriginalDomain Data) Data.F U Data.H q delta tau ell Cmap Cmetric)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hMetric : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart metric i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i))
    (deltaNext : ℝ) (hNext : deltaNext ≠ 0) :
    let nextMap := fun z => oldMap z+U z
    let Hnext := fun p x => (deltaNext^2)⁻¹ •
      (metric p x-inducedMetric (I := 𝓙) (fun y => nextMap (p,y)) x)
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U ∧
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ nextMap ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Hnext i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i)) ∧
    ∀ p x, metric p x-inducedMetric (I := 𝓙) (fun y => nextMap (p,y)) x = deltaNext^2 • Hnext p x := by
  intro nextMap Hnext
  have hU : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U := by
    have hu := hout.joint_smooth
    rw [round3ParameterOriginalDomain_eq_univ Data hd hK] at hu
    exact contMDiffOn_univ.mp hu
  have hn : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ nextMap := hOld.add hU
  have hn' : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ nextMap := by
    rw [modelWithCornersSelf_prod]
    exact hn
  have hInduced := parameterRound2_inducedMetric_originalCoordinates_contDiffOn
    Data.atlas Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth nextMap hn'
  refine ⟨hU,hn,?_,?_⟩
  · intro i
    exact ((hMetric i).sub (hInduced i)).const_smul ((deltaNext^2)⁻¹)
  · intro p x
    dsimp only [Hnext]
    rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hNext),one_smul]

theorem round3Parameter_same_increment_growing_order_budget
    {c : ℕ} (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (q : ℕ) (delta tau ell : ℝ) (Cmap Cmetric : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hout : Round3ParameterJointIncrementConclusion A B S W F U H q delta tau ell Cmap Cmetric)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (k : ℕ) (hk : 10 ≤ k)
    (hdelta : delta = t^k) (htau : tau = t^(6/5 : ℝ)) :
    ∀ rho : ℝ, t ≤ rho/(8*(Cmap (k/2)+1)) →
      paperAtlasCj (k/2) (incrementsOriginalMapCoordinates A B U)
        (incrementsOriginalDifferentiation A B) S ≤ ENNReal.ofReal ((rho/8)*t) := by
  have hu := hout.map0 (k/2)
  rw [hdelta,htau] at hu
  exact (round3_repair_growing_order_budget_of_weighted k (k/2+1) hk (by omega)
    t (Cmap (k/2)) ht ht1 (hCmap (k/2))
    (incrementsOriginalMapCoordinates A B U) (incrementsOriginalDifferentiation A B) S hu.1 hu.2).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_repair_next_map_smooth
#print axioms GlobalEmbedding.Continuation.round3Parameter_same_increment_growing_order_budget
