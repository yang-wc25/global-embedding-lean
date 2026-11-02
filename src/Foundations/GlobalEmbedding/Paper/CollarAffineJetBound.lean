import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local affine pullback of a finite jet

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The real spatial slice is an affine map into the joint complex domain;
its finite jets must be controlled by the actual joint jet norms.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A local C^j jet pulled back by x↦c+Lx has norm at most the original jet norm times ‖L‖^j.

Source: Proposition `prop:collar`, proof lines 530–534, mixed spatial coefficient estimates.
Shift the original map by c. Local C^j regularity supplies an actual open neighborhood on which
the shifted map is C^j. Apply the within-set chain rule for the continuous linear map L there,
then use openness to identify both within-set jets with their full jets. The multilinear
composition norm estimate gives the factor ‖L‖^j. The exact shift identity identifies the
remaining jet with D^j f(c+Lx). No global regularity or completeness is assumed.
-/
theorem collar_affine_jet_bound
    {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (c : E) (L : X →L[𝕜] E) (x : X) (j : ℕ)
    (hf : ContDiffAt 𝕜 j f (c + L x)) :
    ‖iteratedFDeriv 𝕜 j (fun y ↦ f (c + L y)) x‖ ≤
      ‖iteratedFDeriv 𝕜 j f (c + L x)‖ * ‖L‖ ^ j := by
  let h : E → F := fun y ↦ f (c + y)
  have hreg : ContDiffAt 𝕜 j h (L x) :=
    hf.comp (L x) (contDiffAt_const.add contDiffAt_id)
  obtain ⟨U, hU, hxU, hfU⟩ := hreg.contDiffOn' le_rfl (by simp)
  have hfU' : ContDiffOn 𝕜 j h U := by simpa using hfU
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hjet : iteratedFDeriv 𝕜 j (h ∘ L) x =
      (iteratedFDeriv 𝕜 j h (L x)).compContinuousLinearMap (fun _ : Fin j ↦ L) := by
    rw [← iteratedFDerivWithin_of_isOpen j hV hxU,
      ← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact L.iteratedFDerivWithin_comp_right hfU' hU.uniqueDiffOn hV.uniqueDiffOn hxU le_rfl
  change ‖iteratedFDeriv 𝕜 j (h ∘ L) x‖ ≤ _
  rw [hjet]
  have hnorm := (iteratedFDeriv 𝕜 j h (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin j ↦ L)
  simpa only [h, iteratedFDeriv_comp_add_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using hnorm

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_affine_jet_bound
