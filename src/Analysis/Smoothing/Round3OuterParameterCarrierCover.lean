import Smoothing.Round3OuterParameterFixedCarrier
import Probes.Round3ParameterNativeFamily

/-! The fixed carrier has a genuine cover in every nonlinear parameter
observer. Its open pieces are the pullbacks of ORIGINAL nonzero eta sets,
so every quantitative sample is still an actual old eta-support sample.
This closes the cover premise of the all-parameter intrinsic-normal consumer;
no whole-chart derivative bound is inferred from a cutoff-supported bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P A : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype A]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterNativeActiveCarrier (B : OpenPartialHomeomorph P Ep)
    (eta : P × M → ℝ) : Set (Ep × M) :=
  (B.symm.prod (OpenPartialHomeomorph.refl M)).source ∩
    (B.symm.prod (OpenPartialHomeomorph.refl M)) ⁻¹' Function.support eta

theorem round3_parameter_fixed_carrier_native_cover
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := A) (fun p x => Data.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Data g R)
    (host : Fin Data.primaryCount → Fin Data.parameterCount → A → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Fin Data.parameterCount → A → OpenPartialHomeomorph (Ep × D) (Ep × D))
    (hChart : ∀ nu ip a,
      actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a) =
        (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)).chart nu a) :
    let domain := fun nu => round3FixedCarrierDomain (g.eta nu)
    let carrier := fun nu ip a => round3ParameterNativeActiveCarrier (Data.parameterChart ip) (g.eta nu a)
    (∀ nu ip a, IsOpen (carrier nu ip a)) ∧
    (∀ nu ip a, carrier nu ip a ⊆
      (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source) ∧
    (∀ nu ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ domain nu → ∃ a, w ∈ carrier nu ip a) ∧
    (∀ nu ip a w, w ∈ carrier nu ip a →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ tsupport (g.eta nu a)) := by
  intro domain carrier
  have hCar (nu : Fin Data.primaryCount) := round3_fixed_cutoff_carrier
    (I := (𝓘(ℝ,Ep)).prod 𝓙) (g.eta nu) (tsupport (Data.cutoff nu)) R
    (geom.smooth nu) (geom.compact nu) (geom.partition nu) (geom.count nu)
  refine ⟨?_,?_,?_,?_⟩
  · intro nu ip a
    exact (Data.parameterChart ip).symm.prod (OpenPartialHomeomorph.refl M) |>.isOpen_inter_preimage
      (isOpen_ne.preimage (geom.smooth nu a).continuous)
  · intro nu ip a w hw
    have hp : w.1 ∈ (Data.parameterChart ip).target := hw.1.1
    have ha : g.eta nu a ((Data.parameterChart ip).symm w.1,w.2) ≠ 0 := hw.2
    rw [hChart]
    exact (round3ParameterChartPullback_source_iff (Data.parameterChart ip) (g.chart nu a)
      (geom.preserves nu a) w hp).mpr (geom.support nu a (subset_tsupport (g.eta nu a) ha))
  · intro nu ip w hp hw
    obtain ⟨a,ha⟩ := (hCar nu).active _ hw
    exact ⟨a,⟨hp,mem_univ _⟩,ha⟩
  · intro nu ip a w hw
    exact subset_tsupport (g.eta nu a) hw.2

#print axioms round3_parameter_fixed_carrier_native_cover
end GlobalEmbedding.Continuation
