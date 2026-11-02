import Smoothing.Round3OuterParameterCarrierCover
import Probes.Round3ParameterNativeRefinementSamples

/-! The actual fixed all-observer profile controls native chart jets at
every original eta-support sample, without a primary-cutoff nonvanishing
assumption and without any whole-source jet bound. This is the exact
sample class used by the fixed carrier normal construction. -/

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

theorem round3_parameter_carrier_native_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (Forward Inverse Meta : ℕ → ℝ)
    (profiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (nu : Fin Data.primaryCount) (ip : Fin Data.parameterCount) (a : A)
    (host : Fin Data.atlas.count) (b : OpenPartialHomeomorph X X)
    (hChart : actualHostAdaptedChart (Data.atlas.chart host) b =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)).chart nu a)
    (hSource : b.source ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host)).target)
    (k : ℕ) (z : X) (hz : z ∈ b.source)
    (hEval : parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet (host,ip))
    (hEta : ((Data.parameterChart ip).symm z.1,(Data.atlas.chart host).symm z.2) ∈ tsupport (g.eta nu a)) :
    ‖iteratedFDeriv ℝ k b z‖ ≤ Forward k ∧
      ‖iteratedFDeriv ℝ k b.symm (b z)‖ ≤ Inverse k := by
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host)
  let t := q.symm.trans (gN.chart nu a)
  have hh := profiles 1 zero_le_one le_rfl nu a (host,ip) k z hEval hEta
  have hLocal := round3_prepared_host_transition_jets (Data.atlas.chart host) b hSource
  have hForw : iteratedFDeriv ℝ k t z = iteratedFDeriv ℝ k b z := by
    simpa only [hChart] using hLocal.1 k z hz
  have hInv : iteratedFDeriv ℝ k t.symm (b z) = iteratedFDeriv ℝ k b.symm (b z) := by
    simpa only [hChart] using hLocal.2 k (b z) (b.map_source hz)
  have hPoint : t z = b z := by
    change (gN.chart nu a) (q.symm z) = b z
    rw [← hChart]
    change b (q (q.symm z)) = b z
    rw [q.right_inv (hSource hz)]
  change z ∈ t.source ∧ t z ∈ t.target ∧
    1^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
    1^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧ _ at hh
  constructor
  · simpa only [hForw,one_pow,one_mul] using hh.2.2.1
  · simpa only [hPoint,hInv,one_pow,one_mul] using hh.2.2.2.1

#print axioms round3_parameter_carrier_native_jets
end GlobalEmbedding.Continuation
