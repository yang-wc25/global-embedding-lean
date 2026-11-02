import GlobalEmbedding.Paper.CollarCKCompactGermGluing

/-!
# The same actual global Cauchy solution after compact CK gluing

Source: `main.tex`, prop:collar, lines539–550.
DAG: `collar-hopf-global-ck-assembly`; W6 original final-assembly consumer.
This intermediate theorem consumes actual local solutions supplied by W5 and the SAME
H/nu supplied by W4. It constructs no competing local solver, gluer, or Cauchy data.
The original final collar must discharge these honest local inputs using those providers.
-/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- One actual compact gluing call retains the SAME global unknown, actual initial
value/normal derivative, and literal square inverse PDE with actual invertibility.

Apply the accepted compact joint-germ gluer once to the original local family.
At each initial point choose an actual covering local tube, and transfer values and
normal derivatives through its genuine joint germ. At every point of the common
collar, the returned actual local cover supplies a joint germ; the accepted intrinsic
PDE locality theorem transfers that local solution's invertibility and actual inverse
PDE to the SAME global map. No desired metric identity or reselected solution is used.
Source: prop:collar, the common-interval analytic Cauchy solution in lines539–550. -/
theorem collarHopf_global_cauchy_solution_of_local {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {ι : Type*}
    (H ν : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (U : ι → Set (FreeHopfProduct C)) (hU : ∀ i, IsOpen (U i))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (g : ι → ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (hlocal : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω (g i) (Ioo (-(r i)) (r i) ×ˢ U i))
    (hjoint : ∀ i j x, x ∈ U i → x ∈ U j → g i =ᶠ[𝓝 (0, x)] g j)
    (hinitial : ∀ i x, x ∈ U i →
      g i (0, x) = H x ∧ hopfCollarRDeriv (g i) 0 x = ν x)
    (hPDE : ∀ i t x, (t, x) ∈ Ioo (-(r i)) (r i) ×ˢ U i →
      (hopfCollarSquarePairing C (g i) t x).IsInvertible ∧
        deriv (fun s ↦ hopfCollarRDeriv (g i) s x) t =
          (hopfCollarSquarePairing C (g i) t x).inverse
            (hopfCollarSquareForcing C (g i) t x)) :
    ∃ δ > 0, ∃ G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-δ) δ ×ˢ univ) ∧
      (∀ x, G (0, x) = H x ∧ hopfCollarRDeriv G 0 x = ν x) ∧
      ∀ t ∈ Ioo (-δ) δ, ∀ x,
        (hopfCollarSquarePairing C G t x).IsInvertible ∧
          deriv (fun s ↦ hopfCollarRDeriv G s x) t =
            (hopfCollarSquarePairing C G t x).inverse
              (hopfCollarSquareForcing C G t x) := by
  obtain ⟨δ, hδ, G, hG, hcov, hGeq⟩ :=
    collarCK_compact_germ_gluing C U hU r hr g hcover hlocal hjoint
  refine ⟨δ, hδ, G, hG, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    have hz : ((0 : ℝ), x) ∈ Ioo (-δ) δ ×ˢ (univ : Set (FreeHopfProduct C)) :=
      ⟨⟨neg_neg_of_pos hδ, hδ⟩, mem_univ x⟩
    have hzi : ((0 : ℝ), x) ∈ Ioo (-(r i)) (r i) ×ˢ U i :=
      ⟨⟨neg_neg_of_pos (hr i), hr i⟩, hi⟩
    have he : G =ᶠ[𝓝 (0, x)] g i := hGeq i (0, x) hz hzi
    exact ⟨he.self_of_nhds.trans (hinitial i x hi).1,
      (collarCK_rDeriv_germ C (f := G) (g := g i) (z := (0, x)) he).self_of_nhds.trans
        (hinitial i x hi).2⟩
  · intro t ht x
    have hz : (t, x) ∈ Ioo (-δ) δ ×ˢ (univ : Set (FreeHopfProduct C)) :=
      ⟨ht, mem_univ x⟩
    obtain ⟨i, hi⟩ := hcov (t, x) hz
    have he : G =ᶠ[𝓝 (t, x)] g i := hGeq i (t, x) hz hi
    have hp := hPDE i t x hi
    exact collarCK_inversePDE_of_germ C (f := G) (g := g i) (z := (t, x)) he hp.1 hp.2

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarHopf_global_cauchy_solution_of_local
