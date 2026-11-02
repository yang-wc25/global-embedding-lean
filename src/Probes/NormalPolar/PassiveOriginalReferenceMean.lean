import NormalPolar.PassiveOriginalReferenceGeometry
import NormalPolar.PassiveOriginalMeanPreparation

/-! The genuine conditioned reference packet now produces the full-P
canonical native preparation. No separate primary geometry, adapted-chart
identity, inverse identity, source-inner statement or transverse estimate
is requested: all are extracted from that same actual packet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Sub : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IM" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem passiveOriginal_seed_open_slice
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd : IncrementsOriginalDomainConditions seed) (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount) (p : E₀) :
    actualOriginalOpenParameterSlice seed base p = (fun x => seed.F (0,x)) := by
  rw [actualOriginalOpenParameterSlice_eq seed base p
    (hd.parameter_subset (by rw [hAll]; exact mem_univ _))]
  funext x
  change seed.F ((seed.parameterChart base.2).symm p,x) = seed.F (0,x)
  rw [Subsingleton.elim ((seed.parameterChart base.2).symm p) (0 : E₀)]

theorem passiveOriginal_reference_mean_preparation
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀)
    (R : ℕ) (packet : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub R)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B) (Q : Fin B.count → Set Ep)
    (hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i)) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let g := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base R packet
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (hn : IncrementsOriginalFreeNormalConditions Data hd hs),
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data gp Forward Inverse Meta ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
        Nonempty (Round3ParameterOriginalNativeMeanPreparation Data hd hs hn gp ell packet.cT Inverse
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  intro Data g gp hd hs hn
  have hF₀ : ContMDiff IM 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F (0,x)) := by
    rw [← passiveOriginal_seed_open_slice seed hd₀ hAll base 0]
    exact actualOriginalOpenParameterSlice_contMDiff seed hd₀ hs₀ base 0
  have hg := passiveOriginal_reference_primary_geometry seed hd₀ hs₀ hn₀ base R packet hAll hId
  have hdata (nu) (a) : ActualOriginalHostSliceData (seed.atlas.chart (packet.piece nu a).host)
      (packet.piece nu a).native (fun z : E₀ × M => seed.phase nu (0,z.2))
      (packet.piece nu a).slices := by
    have hp : (fun z : E₀ × M => seed.phase nu ((seed.parameterChart base.2).symm z.1,z.2)) =
        (fun z : E₀ × M => seed.phase nu (0,z.2)) := by
      funext z
      rw [Subsingleton.elim ((seed.parameterChart base.2).symm z.1) (0 : E₀)]
    simpa only [hp] using (packet.piece nu a).data
  have hc := passiveOriginalReferencePrimary_chart seed hd₀ hs₀ hn₀ base R packet hId
  apply passiveOriginal_mean_preparation seed hd₀ hF₀ B hB Q hSamples g R hg
    (fun nu a => (packet.piece nu a).host) (fun nu a => (packet.piece nu a).native)
    (fun nu a => (packet.piece nu a).slices) hdata (fun nu a => (hc nu a).symm)
    (fun nu a x => (passiveOriginalReferencePrimary_inverse seed hd₀ hs₀ hn₀ base R packet hId nu a 0 x).symm)
    (fun nu a w hw => packet.source_inner nu a w ((hc nu a) ▸ hw)) packet.cT ?_ hd hs hn
  intro nu a z hz v
  have hz₁ : z.1 = (0 : E₀) := Subsingleton.elim _ _
  have hz₀ : (0,z.2) ∈ (packet.piece nu a).native.target := by
    simpa only [← hz₁] using hz
  have hb := packet.transverse nu a (0,z.2) hz₀ v
  have hBase := passiveOriginal_seed_open_slice seed hd₀ hAll base 0
  simpa only [hBase] using hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_mean_preparation
