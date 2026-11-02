import NormalPolar.ActualProbeInitialSupplyPullback
import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude
import NormalPolar.JointSecondarySource

/-!
# The joint raw secondary is the same physical source in every original chart

The physical parameter is inserted before forming the two joint primary
amplitudes and their negative quadratic forcing. The five primitive source
bindings follow from that construction and the canonical pullback of the
original secondary choice. The identities are only required on the genuine
chart targets, where the supported spatial solver evaluates its inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Ep Λ Β : Type*}
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β] {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem actualProbeInitialSupply_grouped_secondary_binding
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ)
    (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
    (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (geometry : ActualSecondaryRawGeometry
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) n j ell Mg W)
    (host : OpenPartialHomeomorph M D) (cutoff : Ep × M → ℝ)
    (hchoice : ({host := host,chart := geometry.chart,c := geometry.c,cutoff := cutoff} :
      Round3ParameterSecondaryChoice Ep M m) = choice.pullback B) :
    let amplitude := actualProbeInitialGroupedAmplitude F hF g label c vf
      tau delta backgroundLength probeLength a input u
    let source := actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
      (amplitude false) (amplitude true) tau rec choice hc
    let Fbar := fun t => F (B.symm t)
    let hFbar := fun t => hF (B.symm t)
    let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
    let cbar := fun l s t => c l s (B.symm t)
    let vfbar := fun l s t => vf l s (B.symm t)
    let abar := fun l s => round3ParameterChartPullback B (a l s)
    let phases := Sum.elim gbar.phase (fun l z => phase l (B.symm z.1,z.2))
    let nativeAmplitude := jointGroupedCombinedAmplitude Fbar hFbar gbar label cbar vfbar
      tau delta backgroundLength probeLength abar (fun t => input (B.symm t)) (fun t => u (B.symm t))
    let native := jointSecondarySourceOfRawGeometry Fbar hFbar n j ell Mg W geometry host cutoff
      phases (nativeAmplitude false) (nativeAmplitude true) tau rec
    ActualProbeInitialSourcePullbackBinding B source native := by
  intro amplitude source Fbar hFbar gbar cbar vfbar abar phases nativeAmplitude native
  have hp : ∀ l t, t ∈ B.target → ∀ x,
      phases l (t,x) = Sum.elim g.phase phase l (B.symm t,x) := by
    intro l t ht x
    cases l <;> rfl
  have hAmplitude (imag : Bool) : ∀ l t, t ∈ B.target → ∀ x,
      nativeAmplitude imag l (t,x) = amplitude imag l (B.symm t,x) := by
    intro l t ht x
    exact actualProbeInitialSupply_grouped_amplitude_pullback F hF g label c vf tau delta
      backgroundLength probeLength a input u B hg ha imag l t ht x
  have hb := actualProbeInitialSupply_primary_source_binding B (Sum.elim g.phase phase)
    (amplitude false) (amplitude true) phases (nativeAmplitude false) (nativeAmplitude true)
    hp (hAmplitude false) (hAmplitude true) tau rec choice hc
  change ActualProbeInitialSourcePullbackBinding B source
    (actualParameterSecondarySourceOfPrimary phases (nativeAmplitude false) (nativeAmplitude true)
      tau rec {host := host,chart := geometry.chart,c := geometry.c,cutoff := cutoff}
      (jointSecondary_raw_geometry_chart_preserves Fbar hFbar n j ell Mg W geometry))
  simpa only [hchoice] using hb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_secondary_binding
