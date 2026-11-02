import Main.GeneralExactProbeFamily
import Main.GeneralChartSupportedWave

/-!
# Independent statements for the paper's unrestricted paired probes

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition
`defn:legal` and Proposition `prop:probes`, equations (8.1)--(8.2). These
statement definitions import no native analytic producer or final endpoint.

The requested original atlas is quantified before the output. All four
original source norms, both response errors and the smooth orthogonal normal
identification concern the same actual family. The input has no chosen bump
center, radial-cutoff restriction, nonvanishing normal field, global uncut
phase regularity, connectedness or nonemptiness requirement.

`GeneralProbesTarget` allows any legal open neighborhood of the support.
`LocallyPresentedProbesTarget` is its direct form for a cutoff with compact
support on its given open chart. The adapter extends only the cutoff by a
globally smooth zero extension; the phase/normal need be smooth only locally.
Neither declaration asserts existence of the family.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Main
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
universe uM

/-- Full arbitrary-cutoff paired probes in every requested compact smooth
covering atlas, with all scales and native fields recorded explicitly in
`GeneralExactProbeFamily`. The numerical condition is `N ≥ n(n+1)/2+1`. -/
def GeneralProbesTarget : Prop :=
  ∀ {n N : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 2 ≤ n) (_hN : n*(n+1)/2 < N)
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (_hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) F x))
    (_hphase : PhaseRegular F hF)
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (_hA : IsSmoothBufferedAtlas A)
    (_hcompact : ∀ i, IsCompact (A.support i))
    (_hcover : ∀ x, ∃ i, x ∈ A.support i)
    (r : ℕ) (waves : Fin r → OpenSupportedLegalWave F hF),
    Nonempty (GeneralExactProbeFamily F hF A waves)

/-- The exact source proposition with its actual coordinate-chart support
premise. A legal wave is projected into the broader construction entrance
without changing its cutoff, normal, phase, value or tensor. This is the
statement intended for an original `prop:probes` reference. -/
def PaperProbesTarget : Prop :=
  ∀ {n N : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 2 ≤ n) (_hN : n*(n+1)/2 < N)
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (_hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) F x))
    (_hphase : PhaseRegular F hF)
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (_hA : IsSmoothBufferedAtlas A)
    (_hcompact : ∀ i, IsCompact (A.support i))
    (_hcover : ∀ x, ∃ i, x ∈ A.support i)
    (r : ℕ) (waves : Fin r → ChartSupportedLegalWave F hF),
    Nonempty (GeneralExactProbeFamily F hF A
      (fun l => (waves l).toOpenSupportedLegalWave))

/-- The full source presentation with arbitrary compactly supported smooth
cutoffs and local smooth phase/normal germs. Empty M and any finite label
count are independent cases, including a nonempty label set on empty M. -/
def LocallyPresentedProbesTarget : Prop :=
  ∀ {n N : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 2 ≤ n) (_hN : n*(n+1)/2 < N)
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (_hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) F x))
    (_hphase : PhaseRegular F hF)
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (_hA : IsSmoothBufferedAtlas A)
    (_hcompact : ∀ i, IsCompact (A.support i))
    (_hcover : ∀ x, ∃ i, x ∈ A.support i)
    (r : ℕ) (waves : Fin r → LocallyPresentedLegalWave F hF),
    Nonempty (GeneralExactProbeFamily F hF A (fun l => (waves l).toOpenSupported))

/-- This is only an input-presentation conversion, retaining the exact
cutoff-normal value and local native phase covector established by the
zero-extension lemmas. It makes no existence claim by itself. -/
theorem GeneralProbesTarget.toLocallyPresented
    (h : GeneralProbesTarget.{uM}) : LocallyPresentedProbesTarget.{uM} := by
  intro n N M _ _ _ _ _ _ hn hN F hF hi hphase A hA hcompact hcover r waves
  exact h hn hN F hF hi hphase A hA hcompact hcover r
    (fun l => (waves l).toOpenSupported)

/-- Restrict the stronger construction statement to the paper's precise
chart-supported wave class. This proves only the implication between the
statements, not the existence of a general probe producer. -/
theorem GeneralProbesTarget.toPaper
    (h : GeneralProbesTarget.{uM}) : PaperProbesTarget.{uM} := by
  intro n N M _ _ _ _ _ _ hn hN F hF hi hphase A hA hcompact hcover r waves
  exact h hn hN F hF hi hphase A hA hcompact hcover r
    (fun l => (waves l).toOpenSupportedLegalWave)

end GlobalEmbedding.Main

#print axioms GlobalEmbedding.Main.GeneralProbesTarget.toLocallyPresented

#print axioms GlobalEmbedding.Main.GeneralProbesTarget.toPaper
