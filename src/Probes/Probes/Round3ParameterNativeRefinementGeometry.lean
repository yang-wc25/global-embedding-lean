import Probes.Round3ParameterOriginalPrimaryGeometry
import Probes.Round3ParameterNativeFamily

/-! Every observer parameter chart receives the same global physical eta
partition, including ordinary germs and the original overlap count. The
native domain may be any actual open subset of that chart target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem round3Parameter_plain_pullback_tsupport
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (q : OpenPartialHomeomorph A B) (f : A → ℝ) (y : B)
    (hy : y ∈ q.target) (hf : y ∈ tsupport (fun z => f (q.symm z))) :
    q.symm y ∈ tsupport f := by
  by_contra hn
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (q.symm.continuousOn.continuousAt (q.open_target.mem_nhds hy))
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hf

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_native_primary_refinement_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (R : ℕ) (hg : Round3ParameterOriginalPrimaryGeometry Data g R)
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (W : Set (Ep × M)) (hW : IsOpen W) (hWB : W ⊆ B.target ×ˢ (univ : Set M)) :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g B
    (∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (gN.eta nu a) W) ∧
    (∀ nu a, incrementsGlobalRelativeSupport W (gN.eta nu a) ⊆ (gN.chart nu a).source) ∧
    (∀ nu z, z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ a, gN.eta nu a w = 1) ∧
    (∀ nu z, z ∈ W → (Finset.univ.filter (fun a => z ∈ incrementsGlobalRelativeSupport W (gN.eta nu a))).card ≤ R) ∧
    ∀ z, z ∈ W → (Finset.univ.filter (fun nu => z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu))).card ≤ Data.primaryCount := by
  intro gN
  let q := round3ParameterProductChart (M := M) B
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm W :=
    (round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B hB).mono hWB
  have hEta (nu : Fin Data.primaryCount) (a : Sub) (z : Ep × M)
      (hz : z ∈ incrementsGlobalRelativeSupport W (gN.eta nu a)) :
      (B.symm z.1,z.2) ∈ tsupport (g.eta nu a) := by
    rw [parameterRound2_global_relativeSupport_eq W hW] at hz
    exact round3Parameter_plain_pullback_tsupport q (g.eta nu a) z (hWB hz.1) hz.2
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro nu a
    exact (hg.smooth nu a).comp_contMDiffOn hq
  · intro nu a z hz
    have hzW : z ∈ W := by
      rw [parameterRound2_global_relativeSupport_eq W hW] at hz
      exact hz.1
    exact (round3ParameterChartPullback_source_iff B (g.chart nu a) (hg.preserves nu a) z
      (hWB hzW).1).mpr (hg.support nu a (hEta nu a z hz))
  · intro nu z hz
    rw [parameterRound2_global_relativeSupport_eq W hW] at hz
    have hp : (B.symm z.1,z.2) ∈ tsupport (Data.cutoff nu) := by
      have hh := round3Parameter_plain_pullback_tsupport q (g.cutoff nu) z (hWB hz.1) hz.2
      rwa [hg.cutoff] at hh
    have ht : Tendsto q.symm (𝓝 z) (𝓝 (q.symm z)) :=
      q.symm.continuousOn.continuousAt (q.open_target.mem_nhds (hWB hz.1))
    exact ht.eventually (hg.partition nu (q.symm z) hp)
  · intro nu z hz
    apply (Finset.card_le_card ?_).trans (hg.count nu (B.symm z.1,z.2))
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hEta nu a z (Finset.mem_filter.mp ha).2⟩
  · intro z hz
    exact (Finset.card_filter_le _ _).trans_eq (by simp)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_plain_pullback_tsupport
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_primary_refinement_geometry
