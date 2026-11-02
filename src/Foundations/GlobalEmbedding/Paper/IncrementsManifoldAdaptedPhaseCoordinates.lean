import GlobalEmbedding.Paper.IncrementsLocalAdaptedPhaseCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# ORIGINAL-manifold local adapted chart: actual native transport

Source: `main.tex`, lem:increments594–617 and finite auxiliary parameters.
DAG: `increments-manifold-adapted-phase-coordinates`. Exclusive worker W2.
STAGE2 ONLY for ROOT exact lock; the sole named proof hole is expected.
Calls the canonical normed producer. No IFT, kernel packing or slice reproof.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [FiniteDimensional ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "𝓙" => 𝓘(ℝ, D)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]

/-- The ORIGINAL joint phase yields ONE actual original-manifold local adapted
chart by transporting the accepted normed producer through the genuine original
spatial chart. Bothway joint smoothness is proved, never an output hypothesis.

Natural-language proof, pending ROOT exact lock: take native q=id.prod c and
restrict it to the ORIGINAL W with restrOpen. Its actual source is the original
product chart source intersect W, and its literal target is open. Compose the
original joint phase with the genuine inverse product chart to obtain actual
coordinate phase Phi(p,y)=psi p(c.symm y), smooth only on that actual target.
The coordinate base (z0.1,c z0.2) lies there, and the explicit coordinate-slice
noncriticality is exactly canonical W5's input. Call the accepted
increments_exists_local_adapted_phase_coordinates ONCE. Compose the restricted
original product chart with that SAME normed local chart using native trans.
Native domains retain the original base and source inside W. Genuine chart
and inverse-chart smoothness from maximalAtlas, accepted normed bothway
smoothness and native composition prove the actual output's joint smoothness.
The original chart inverse laws and accepted p/literalphase identities give
the original-manifold source and target identities. No IFT, new inverse choice,
kernel packing, slice or atlas proof is repeated.

The source paper's nonzero manifold covector to this explicit coordinate-slice
noncriticality remains a genuine caller obligation unless reused canonically;
it is not silently discharged or added to the original final target. No global
parameter extension, nonempty every-p chart, CompactM, quantitative radius,
cover/profile/conditioning/threshold or full increments assertion is added.
Source: original adapted coordinates and finite-parameter clause, lem:increments.
Parameter dimension zero, m=0 and disconnected original M are allowed. -/
theorem increments_exists_manifold_local_adapted_phase_coordinates
    (c : OpenPartialHomeomorph M D)
    (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (ψ : Ep → M → ℝ) (W : Set (Ep × M)) (hW : IsOpen W)
    (z₀ : Ep × M) (hz₀ : z₀ ∈ W) (hc₀ : z₀.2 ∈ c.source)
    (hψ : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (Function.uncurry ψ) W)
    (hcritical : fderiv ℝ (fun y : D ↦ ψ z₀.1 (c.symm y)) (c z₀.2) ≠ 0) :
    ∃ a : OpenPartialHomeomorph (Ep × M) (Ep × D),
      z₀ ∈ a.source ∧ a.source ⊆ W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, Ep × D) ∞ a a.source ∧
      ContMDiffOn 𝓘(ℝ, Ep × D) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = ψ z.1 z.2) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧
        ψ (a.symm z).1 (a.symm z).2 = z.2 0) := by
  let q := ((OpenPartialHomeomorph.refl Ep).prod c).restrOpen W hW
  have hqs (z : Ep × M) (hz : z ∈ q.source) : z ∈ W := hz.2
  have hqc (z : Ep × M) (hz : z ∈ q.source) : z.2 ∈ c.source := hz.1.2
  have hqt (z : Ep × D) (hz : z ∈ q.target) : z.2 ∈ c.target := hz.1.2
  have hq₀ : z₀ ∈ q.source := ⟨⟨mem_univ _, hc₀⟩, hz₀⟩
  have hq : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, Ep × D) ∞ q q.source := by
    have hcs : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓙 ∞
        (fun z : Ep × M ↦ c z.2) q.source :=
      (contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_snd.contMDiffOn hqc
    exact contMDiffOn_fst.prodMk_space hcs
  have hqi : ContMDiffOn 𝓘(ℝ, Ep × D) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞
        (fun z : Ep × D ↦ c.symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
        contDiff_snd.contMDiff.contMDiffOn hqt
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  have hΦ : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ ψ z.1 (c.symm z.2)) q.target :=
    (hψ.comp hqi (fun z hz ↦ hqs _ (q.map_target hz))).contDiffOn
  obtain ⟨b, hb₀, hbsub, hb, hbi, hbf, hbif⟩ :=
    increments_exists_local_adapted_phase_coordinates
      (fun z : Ep × D ↦ ψ z.1 (c.symm z.2)) q.target q.open_target
      (q z₀) (q.map_source hq₀) hΦ hcritical
  refine ⟨q.trans b, ⟨hq₀, hb₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hqs z hz.1
  · exact hb.contMDiffOn.comp (hq.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  · exact hqi.comp (hbi.contMDiffOn.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  · intro z hz
    have h := hbf (q z) hz.2
    refine ⟨h.1, ?_⟩
    change (b (q z)).2 0 = ψ z.1 z.2
    rw [h.2]
    change ψ z.1 (c.symm (c z.2)) = ψ z.1 z.2
    rw [c.left_inv (hqc z hz.1)]
  · intro z hz
    have h := hbif z hz.1
    exact ⟨h.1, h.2⟩

/-- ORIGINAL nonzero spatial mfderiv produces the SAME actual local adapted
joint chart, choosing its genuine original atlas chart internally. The old
coordinate noncriticality caller is derived here, not a new input hypothesis.

Natural-language proof, pending ROOT exact lock: choose the native original
chartAt D z0.2 (equivalently its self-model extended chart), with native
maximalAtlas infinity and base-source membership. Native mfderiv and
writtenInExtChartAt express the actual original phase covector through the
inverse-chart coordinate derivative and genuine tangent cast equivalences.
Coordinate fderiv zero would force original mfderiv zero, including the native
non-differentiable zero branch; alternatively use the actual chain equation
and chart/inverse differential cancellation as in the accepted original phase
covector proof. Thus the required coordinate fderiv is genuinely nonzero.
Invoke the existing accepted
increments_exists_manifold_local_adapted_phase_coordinates ONCE for that SAME
original chart, original joint phase, open W and base. Return its exact a,
base membership, source inclusion, actual bothway joint smoothness and literal
parameter/phase/inverse identities. The accepted earlier header/doc/body is
unchanged; no IFT, kernel packing, transport or slice proof is repeated.

Only original joint phase regularity on original W and original spatial
noncriticality are inputs. No chosen chart, coordinate derivative, output
chart/regularity, global parameter extension, compactness or nonempty every-p
slice is assumed. Original uniform cover/admissibility/conditioning/profile/
validity threshold and full increments remain separate. Source: original
noncritical phases, adapted coordinates and finite parameters, main.tex594–617.
Parameter dimension zero, m=0 and disconnected original M are allowed. -/
theorem increments_exists_manifold_local_adapted_phase_coordinates_of_mfderiv_ne_zero
    (ψ : Ep → M → ℝ) (W : Set (Ep × M)) (hW : IsOpen W)
    (z₀ : Ep × M) (hz₀ : z₀ ∈ W)
    (hψ : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (Function.uncurry ψ) W)
    (hcritical : mfderiv 𝓙 𝓘(ℝ, ℝ) (ψ z₀.1) z₀.2 ≠ 0) :
    ∃ a : OpenPartialHomeomorph (Ep × M) (Ep × D),
      z₀ ∈ a.source ∧ a.source ⊆ W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, Ep × D) ∞ a a.source ∧
      ContMDiffOn 𝓘(ℝ, Ep × D) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = ψ z.1 z.2) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧
        ψ (a.symm z).1 (a.symm z).2 = z.2 0) := by
  classical
  let c : OpenPartialHomeomorph M D := chartAt D z₀.2
  have hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓙) (n := ∞) z₀.2
  have hc₀ : z₀.2 ∈ c.source := mem_chart_source D z₀.2
  have hcoord : fderiv ℝ (fun y : D ↦ ψ z₀.1 (c.symm y)) (c z₀.2) ≠ 0 := by
    intro hzero
    have hd : fderivWithin ℝ (writtenInExtChartAt 𝓙 𝓘(ℝ, ℝ) z₀.2 (ψ z₀.1))
        (range 𝓙) (extChartAt 𝓙 z₀.2 z₀.2) = 0 := by
      simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
      exact hzero
    apply hcritical
    rw [mfderiv]
    split_ifs
    · rw [hd]
      simp
    · rfl
  exact increments_exists_manifold_local_adapted_phase_coordinates
    c hc ψ W hW z₀ hz₀ hc₀ hψ hcoord

end GlobalEmbedding.Paper
