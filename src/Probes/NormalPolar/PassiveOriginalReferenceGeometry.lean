import NormalPolar.PassiveZeroParameterChart
import Probes.Round3PreparedReferencePrimaryPacket
import Probes.Round3ParameterOriginalPrimaryGeometry

/-! The actual conditioned reference packet supplies the zero-parameter
original primary family and its complete geometry. Its subordinate cutoffs,
adapted charts and slices are retained literally; its true local partition
on the whole zero-parameter set supplies the global original partition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M Sub : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)

variable (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
  (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
  (hn : IncrementsOriginalFreeNormalConditions seed hd hs)
  (base : Fin seed.atlas.count × Fin seed.parameterCount) (R : ℕ)
  (packet : Round3PreparedReferencePrimaryPacket seed hd hs hn base Sub R)

def passiveOriginalReferencePrimary : Round3ParameterPrimaryFamily (I := IM) (m := m)
    (Λ := Fin seed.primaryCount) (Β := Sub) (fun p x => seed.F (p,x)) :=
  round3ParameterOriginalPrimaryFamily seed hd hs hn (fun _ _ => base.2)
    (fun _ _ => seed.parameterOpen ×ˢ (univ : Set M)) packet.piece

theorem passiveOriginalReferencePrimary_eta
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀) (nu) (a) :
    (passiveOriginalReferencePrimary seed hd hs hn base R packet).eta nu a =
      (packet.piece nu a).cutoff := by
  funext z
  simp only [passiveOriginalReferencePrimary,round3ParameterOriginalPrimaryFamily,hId,
    OpenPartialHomeomorph.refl_source,mem_univ,if_true,OpenPartialHomeomorph.refl_apply,id_eq]

theorem passiveOriginalReferencePrimary_chart
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀) (nu) (a) :
    (passiveOriginalReferencePrimary seed hd hs hn base R packet).chart nu a =
      actualHostAdaptedChart (seed.atlas.chart (packet.piece nu a).host)
        (packet.piece nu a).native := by
  change round3ParameterChartPullback (seed.parameterChart base.2).symm _ = _
  rw [hId,OpenPartialHomeomorph.refl_symm,passiveParameter_pullback_refl]

theorem passiveOriginalReferencePrimary_inverse
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀) (nu) (a) (p : E₀) (x : D) :
    (passiveOriginalReferencePrimary seed hd hs hn base R packet).inverse nu a p x =
      ((packet.piece nu a).slices p).symm x := by
  change ((packet.piece nu a).slices ((seed.parameterChart base.2) p)).symm x = _
  rw [hId,OpenPartialHomeomorph.refl_apply]
  rfl

theorem passiveOriginal_reference_primary_geometry
    (hAll : seed.parameterSet = univ)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀) :
    Round3ParameterOriginalPrimaryGeometry seed
      (passiveOriginalReferencePrimary seed hd hs hn base R packet) R := by
  let g := passiveOriginalReferencePrimary seed hd hs hn base R packet
  have he := passiveOriginalReferencePrimary_eta seed hd hs hn base R packet hId
  have hc := passiveOriginalReferencePrimary_chart seed hd hs hn base R packet hId
  have hG : (univ : Set (E₀ × M)) ⊆ packet.parameterDomain ×ˢ (univ : Set M) := by
    intro z hz
    exact ⟨packet.parameter_contains (by rw [hAll]; trivial),mem_univ _⟩
  have ctrl := packet.samples 0 le_rfl zero_le_one univ isOpen_univ hG
  refine {
    phase := rfl
    cutoff := rfl
    normal := rfl
    linear := rfl
    preserves := round3ParameterOriginalPrimaryFamily_preserves seed hd hs hn _ _ _
    inverse := fun nu a z hz => round3ParameterLiftedPrimaryChart_inverse seed base.2 nu _
      (packet.piece nu a) z hz
    phase_coordinate := fun nu a z hz => round3ParameterLiftedPrimaryChart_phase seed base.2 nu _
      (packet.piece nu a) z hz
    inverse_active := fun nu a z hz => round3ParameterLiftedPrimaryChart_active seed base.2 nu _
      (packet.piece nu a) z hz
    smooth := ?_
    compact := ?_
    support := ?_
    partition := ?_
    count := ?_ }
  · intro nu a
    rw [he nu a]
    exact (packet.piece nu a).smooth
  · intro nu a
    rw [he nu a]
    exact (packet.piece nu a).compact
  · intro nu a
    rw [he nu a,hc nu a]
    exact (packet.piece nu a).support
  · intro nu z hz
    have hz' : z ∈ incrementsGlobalRelativeSupport univ
        (fun w : E₀ × M => seed.cutoff nu ((seed.parameterChart base.2).symm w.1,w.2)) := by
      simpa only [parameterRound2_global_relativeSupport_eq univ isOpen_univ,hId,
        OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,univ_inter] using hz
    have hh := ctrl.partition nu z hz'
    simpa only [actualOriginalPrimaryFamily,he] using hh
  · intro nu z
    have hh := ctrl.eta_count nu z (mem_univ _)
    simpa only [actualOriginalPrimaryFamily,he,
      parameterRound2_global_relativeSupport_eq univ isOpen_univ,univ_inter] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_primary_geometry
