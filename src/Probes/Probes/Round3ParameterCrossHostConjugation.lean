import Probes.Round3ParameterNativeChartSmooth

/-! Exact host factorization of the canonical cross-parameter chart.
The two original parameter charts appear as C=Bpiece.symm.trans Bobserver.
The resulting OpenPartialHomeomorph is equal, including its genuine source
and both global function representatives, to the twice-conjugated physical
chart. This is the entrance to the original native raw producer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

def round3ParameterCrossNativeChart
    (Bpiece Bobserver : OpenPartialHomeomorph P Ep) (b : OpenPartialHomeomorph X X) :
    OpenPartialHomeomorph X X := round3ParameterChartPullback (Bpiece.symm.trans Bobserver) b

theorem round3Parameter_host_native_preserves
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (hb : Round3ParameterChartPreserves b) :
    Round3ParameterChartPreserves (actualHostAdaptedChart c b) :=
  fun z hz => hb (z.1,c z.2) hz.2

theorem round3Parameter_cross_host_conjugation
    (Bpiece Bobserver : OpenPartialHomeomorph P Ep) (c : OpenPartialHomeomorph M D)
    (b : OpenPartialHomeomorph X X) (hb : Round3ParameterChartPreserves b) :
    actualHostAdaptedChart c (round3ParameterCrossNativeChart Bpiece Bobserver b) =
      round3ParameterChartPullback Bobserver
        (round3ParameterChartPullback Bpiece.symm (actualHostAdaptedChart c b)) := by
  let C := Bpiece.symm.trans Bobserver
  let a := actualHostAdaptedChart c b
  let aP := round3ParameterChartPullback Bpiece.symm a
  have ha : Round3ParameterChartPreserves a := round3Parameter_host_native_preserves c b hb
  have haP : Round3ParameterChartPreserves aP := round3ParameterChartPullback_preserves Bpiece.symm a ha
  apply OpenPartialHomeomorph.ext
  · intro z
    rfl
  · intro z
    rfl
  · ext z
    constructor
    · intro hz
      have hzHost : z.2 ∈ c.source := hz.1.2
      have hzCross : (z.1,c z.2) ∈ (round3ParameterChartPullback C b).source := hz.2
      have hh := (round3ParameterChartPullback_source C b (z.1,c z.2)).mp hzCross
      have hBobs : z.1 ∈ Bobserver.target := hh.1.1
      have hBpiece : Bobserver.symm z.1 ∈ Bpiece.source := hh.1.2
      have hbPoint : (Bpiece (Bobserver.symm z.1),c z.2) ∈ b.source := hh.2.1
      have hA : (Bpiece (Bobserver.symm z.1),z.2) ∈ a.source :=
        ⟨⟨mem_univ _,hzHost⟩,hbPoint⟩
      have hAP : (Bobserver.symm z.1,z.2) ∈ aP.source :=
        (round3ParameterChartPullback_source_iff Bpiece.symm a ha (Bobserver.symm z.1,z.2) hBpiece).mpr hA
      exact (round3ParameterChartPullback_source_iff Bobserver aP haP z hBobs).mpr hAP
    · intro hz
      have ho := (round3ParameterChartPullback_source Bobserver aP z).mp hz
      have hp := (round3ParameterChartPullback_source Bpiece.symm a (Bobserver.symm z.1,z.2)).mp ho.2.1
      have hC : z.1 ∈ C.target := ⟨ho.1,hp.1⟩
      refine ⟨⟨mem_univ _,hp.2.1.1.2⟩,?_⟩
      exact (round3ParameterChartPullback_source_iff C b hb (z.1,c z.2) hC).mpr hp.2.1.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_cross_host_conjugation
