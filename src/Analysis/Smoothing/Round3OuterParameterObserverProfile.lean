import Smoothing.Round3OuterFixedObserverJets
import Smoothing.Round3OuterParameterNormalCover

/-! The actual original observer map of a host normal cover has a fixed
profile. The overlap, sample and map conditions are proved from the genuine
adapted source. Constants use only the fixed original packet and the fixed
reference forward-chart profile. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ

theorem round3_parameter_host_observer_fixed_profile
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (host : Fin Data.atlas.count)
    (b : OpenPartialHomeomorph X X) (hb : ContDiffOn ℝ ∞ b b.source)
    (carrier : Set (Ep × M)) (hCarrierOpen : IsOpen carrier)
    (hCarrierSub : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart host) b).source)
    (j : ℕ) (budget Bforward : ℝ) (hBforward : 0 ≤ Bforward)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ budget)
    (hForward : ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ∩
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (round3OriginalNativeObserverPoint Data i) ⁻¹' carrier),
      ‖iteratedFDeriv ℝ k b
        ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host))
          (round3OriginalNativeObserverPoint Data i y))‖ ≤ Bforward) :
    let chart := actualHostAdaptedChart (Data.atlas.chart host) b
    let point := round3OriginalNativeObserverPoint Data i
    let U := incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩ point ⁻¹' carrier
    ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ∩ U,
      ‖iteratedFDeriv ℝ k (chart ∘ point) y‖ ≤
        (actualFastChartTransferCost
          (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d j*budget) k*Bforward)*
            linearModelFactor (parameterTensorModelEquiv (m+1) d).symm k := by
  intro chart point U
  let a := parameterTensorModelEquiv (m+1) d
  let Un := a ⁻¹' U
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ∩ U
  let Sn := a ⁻¹' S
  have hU : IsOpen U := (round3_original_native_observer_smooth Data hd i).continuousOn.isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i) hCarrierOpen
  have hpoint (z : X) : point (a z) = (z.1,(Data.atlas.chart i.1).symm z.2) := by
    exact congrArg (fun w : X => (w.1,(Data.atlas.chart i.1).symm w.2))
      ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  have hOverlap : Un ⊆ actualOriginalNativeGivenTransitionDomain Data (i,(host,i.2)) := by
    intro z hz
    refine ⟨hz.1,?_,?_⟩
    · exact (Data.parameterChart i.2).map_target hz.1.2
    · exact (hCarrierSub hz.2).1.2
  have hMap : MapsTo (actualOriginalObserverHostTransition Data i host) Un b.source := by
    intro z hz
    have hh := (hCarrierSub hz.2).2
    change (actualOriginalHostJointChart (Data.atlas.chart host)) (point (a z)) ∈ b.source at hh
    rw [hpoint] at hh
    exact hh
  have hSample : ∀ z ∈ Sn, a z ∈ actualOriginalGivenTransitionSample Data (i,(host,i.2)) :=
    fun z hz => ⟨hz.1,hOverlap hz.2⟩
  have hNative := round3_original_fixed_observer_adapted_positive_jets Data hd i host b hb
    Un Sn (hU.preimage a.continuous) (fun _ hz => hz.2) hOverlap hMap hSample
    j 1 budget Bforward (by norm_num) hBforward hfinite hbudget
    (by
      intro k hk hkj z hz
      have hh := hForward k hk hkj (a z) hz
      change ‖iteratedFDeriv ℝ k b
        ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host)) (point (a z)))‖ ≤ Bforward at hh
      rw [hpoint] at hh
      change ‖iteratedFDeriv ℝ k b (actualOriginalObserverHostTransition Data i host z)‖ ≤ Bforward at hh
      simpa only [one_pow,one_mul] using hh)
  let phi := fun z : X => chart (z.1,(Data.atlas.chart i.1).symm z.2)
  have heq : chart ∘ point = phi ∘ a.symm := by
    funext y
    have hh := hpoint (a.symm y)
    rw [a.apply_symm_apply] at hh
    exact congrArg chart hh
  intro k hk hkj y hy
  rw [heq]
  have hsn : a.symm y ∈ Sn := by change a (a.symm y) ∈ S; rwa [a.apply_symm_apply]
  have hBound := hNative.2 k hk hkj (a.symm y) hsn
  simp only [one_pow,one_mul] at hBound
  exact (norm_iteratedFDeriv_comp_equiv_le a.symm phi k y).trans
    (mul_le_mul_of_nonneg_right hBound (linearModelFactor_nonneg _ _))

#print axioms round3_parameter_host_observer_fixed_profile
end GlobalEmbedding.Continuation
