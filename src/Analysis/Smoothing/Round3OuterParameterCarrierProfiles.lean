import Smoothing.Round3OuterParameterCarrierNativeJets
import Smoothing.Round3OuterParameterNormalCover

/-! Both quantitative hypotheses of the actual all-parameter normal cover
are consequences of the fixed original all-observer profiles on the
constructed carrier. No current-SF compact maximum is taken. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P A : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype A]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_parameter_fixed_carrier_normal_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Data g R)
    (Forward Inverse Meta : ℕ → ℝ)
    (profiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (host : Fin Data.primaryCount → Fin Data.parameterCount → A → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Fin Data.parameterCount → A → OpenPartialHomeomorph X X)
    (hChart : ∀ nu ip a,
      actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a) =
        (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)).chart nu a)
    (hSource : ∀ nu ip a, (b nu ip a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu ip a))).target)
    (hInner : ∀ nu ip a w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Data.atlas.inner (host nu ip a)) :
    let carrier := fun nu ip a => round3ParameterNativeActiveCarrier (Data.parameterChart ip) (g.eta nu a)
    (∀ nu ip a k z, z ∈ (b nu ip a).target ∩
      (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).symm ⁻¹' carrier nu ip a →
      parameterTensorModelEquiv (m+1) d ((b nu ip a).symm z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host nu ip a,ip) →
      ‖iteratedFDeriv ℝ k (b nu ip a).symm z‖ ≤ Inverse k) ∧
    (∀ nu (i : Fin Data.atlas.count × Fin Data.parameterCount) a k y,
      y ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ∩
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (round3OriginalNativeObserverPoint Data i) ⁻¹' carrier nu i.2 a) →
      ‖iteratedFDeriv ℝ k (b nu i.2 a)
        ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu i.2 a)))
          (round3OriginalNativeObserverPoint Data i y))‖ ≤ Forward k) := by
  intro carrier
  have hCover := round3_parameter_fixed_carrier_native_cover Data g R geom host b hChart
  constructor
  · intro nu ip a k z hz hEval
    have hEta : ((Data.parameterChart ip).symm ((b nu ip a).symm z).1,
        (Data.atlas.chart (host nu ip a)).symm ((b nu ip a).symm z).2) ∈
        tsupport (g.eta nu a) :=
      hCover.2.2.2 nu ip a _ hz.2
    have hh := round3_parameter_carrier_native_jets Data g Forward Inverse Meta profiles
      nu ip a (host nu ip a) (b nu ip a) (hChart nu ip a) (hSource nu ip a) k
      ((b nu ip a).symm z) ((b nu ip a).map_target hz.1) hEval hEta
    simpa only [(b nu ip a).right_inv hz.1] using hh.2
  · intro nu i a k y hy
    let w := round3OriginalNativeObserverPoint Data i y
    let c := Data.atlas.chart (host nu i.2 a)
    let q := actualOriginalHostJointChart («Ep» := Ep) c
    let z := q w
    have hw : w ∈ carrier nu i.2 a := hy.2.2
    have hsrc := hCover.2.1 nu i.2 a hw
    have hinner := hInner nu i.2 a w hsrc
    have hz : z ∈ (b nu i.2 a).source := hsrc.2
    have hEvalOld := (actual_original_native_evaluation_iff Data hd i
      ((parameterTensorModelEquiv (m+1) d).symm y)).mp
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy.1)
    have hEval : parameterTensorModelEquiv (m+1) d z ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet (host nu i.2 a,i.2) := by
      apply (actual_original_native_evaluation_iff Data hd (host nu i.2 a,i.2) z).mpr
      exact ⟨hd.source_inner_norm (host nu i.2 a) w.2 hinner,hEvalOld.2⟩
    have hEta : ((Data.parameterChart i.2).symm z.1,c.symm z.2) ∈ tsupport (g.eta nu a) := by
      change ((Data.parameterChart i.2).symm w.1,c.symm (c w.2)) ∈ _
      rw [c.left_inv (Data.atlas.inner_subset (host nu i.2 a) hinner)]
      exact hCover.2.2.2 nu i.2 a w hw
    exact (round3_parameter_carrier_native_jets Data g Forward Inverse Meta profiles
      nu i.2 a (host nu i.2 a) (b nu i.2 a) (hChart nu i.2 a) (hSource nu i.2 a)
      k z hz hEval hEta).1

#print axioms round3_parameter_fixed_carrier_normal_profiles
end GlobalEmbedding.Continuation
