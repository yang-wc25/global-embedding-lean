import GlobalEmbedding.Paper.PlanarProjectorPrincipalSlice
import GlobalEmbedding.Paper.PlanarJetFieldEvaluation
import GlobalEmbedding.External.SphereEversion.Global.Relation

/-!
# The actual open-ample projector maps relation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
The relation lives on the genuine imported native one-jet bundle and uses its actual
principal derivative slices. No genuine solution is an input to these relation properties.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section NativeRelation

variable {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The literal ambient-projector pair evaluated on a genuine native first jet.
In the actual projective application Q is the derivative of P along the descended Hopf field. -/
def planarProjectorJetValue
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _))
    (P Q : M → E →L[ℝ] E)
    (σ : OneJetBundle I M 𝓘(ℝ, ℝ × E) (ℝ × E)) : ℝ × E :=
  let u := NormedSpace.fromTangentSpace σ.1.2 (σ.2 (X σ.1.1))
  (u.1, P σ.1.1 u.2 + P σ.1.1 (Q σ.1.1 σ.1.2.2))

/-- The actual open first-order maps relation used for constructing the initial planar map. -/
def planarProjectorJetRelation
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _))
    (P Q : M → E →L[ℝ] E) : RelMfld I M 𝓘(ℝ, ℝ × E) (ℝ × E) :=
  {σ | planarProjectorJetValue X P Q σ ≠ 0}

/-- The actual projector pair is native smooth on the actual imported one-jet bundle,
directly from the true field and smooth coefficient fields. -/
theorem contMDiff_planarProjectorJetValue
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _))
    (P Q : M → E →L[ℝ] E)
    (hP : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ P)
    (hQ : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ Q) :
    ContMDiff ((I.prod 𝓘(ℝ, ℝ × E)).prod 𝓘(ℝ, V →L[ℝ] ℝ × E))
      𝓘(ℝ, ℝ × E) ∞ (planarProjectorJetValue X P Q) := by
  have hproj := contMDiff_oneJetBundle_proj (I := I) (I' := 𝓘(ℝ, ℝ × E))
    (M := M) (M' := ℝ × E)
  have hx := hproj.fst
  have hy := hproj.snd
  have hu := contMDiff_oneJetFieldEval (F := ℝ × E) X
  have hu₀ := (ContinuousLinearMap.fst ℝ ℝ E).contDiff.contMDiff.comp hu
  have hu₁ := (ContinuousLinearMap.snd ℝ ℝ E).contDiff.contMDiff.comp hu
  have hw := (ContinuousLinearMap.snd ℝ ℝ E).contDiff.contMDiff.comp hy
  have hpx := hP.comp hx
  have hqx := hQ.comp hx
  have hsecond := (hpx.clm_apply hu₁).add (hpx.clm_apply (hqx.clm_apply hw))
  apply (contMDiff_prod_module_iff _).mpr
  exact ⟨hu₀, hsecond⟩

/-- Nonvanishing of the actual smooth projector pair defines an open native jet relation. -/
theorem isOpen_planarProjectorJetRelation
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _))
    (P Q : M → E →L[ℝ] E)
    (hP : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ P)
    (hQ : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ Q) :
    IsOpen (planarProjectorJetRelation X P Q) := by
  exact (contMDiff_planarProjectorJetValue X P Q hP hQ).continuous.isOpen_preimage
    {0}ᶜ isClosed_singleton.isOpen_compl

/-- The actual native maps relation is ample when P is pointwise the actual rank-one
orthogonal projector. A unit representative is chosen only for the proof of each slice;
no global representative or trivialization of the projective line is assumed. -/
theorem ample_planarProjectorJetRelation [FiniteDimensional ℝ E]
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _))
    (P Q : M → E →L[ℝ] E)
    (hP : ∀ x : M, ∃ z : E, ‖z‖ = 1 ∧ ∀ w, P x w = ⟪z, w⟫ • z) :
    (planarProjectorJetRelation X P Q).Ample := by
  intro σ p
  obtain ⟨z, hz, hzP⟩ := hP σ.1.1
  let _ : NormedAddCommGroup (TangentSpace I σ.1.1) :=
    inferInstanceAs (NormedAddCommGroup V)
  let _ : NormedSpace ℝ (TangentSpace I σ.1.1) := inferInstanceAs (NormedSpace ℝ V)
  let _ : NormedAddCommGroup (TangentSpace 𝓘(ℝ, ℝ × E) σ.1.2) :=
    inferInstanceAs (NormedAddCommGroup (ℝ × E))
  let _ : NormedSpace ℝ (TangentSpace 𝓘(ℝ, ℝ × E) σ.1.2) :=
    inferInstanceAs (NormedSpace ℝ (ℝ × E))
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) σ.1.2
  let L : TangentSpace I σ.1.1 →L[ℝ] TangentSpace 𝓘(ℝ, ℝ × E) σ.1.2 := σ.2
  let φ : TangentSpace I σ.1.1 →L[ℝ] ℝ × E := e.toContinuousLinearMap.comp L
  let c : ℝ × ℝ := (0, ⟪z, Q σ.1.1 σ.1.2.2⟫)
  have hs := planarProjector_update_ample z hz p φ (X σ.1.1) c
  have ht := hs.preimage e.toContinuousAffineEquiv
  have hupdate (u : TangentSpace 𝓘(ℝ, ℝ × E) σ.1.2) :
      e (p.update L u (X σ.1.1)) = p.update φ (e u) (X σ.1.1) := by
    exact congrArg (fun A : TangentSpace I σ.1.1 →L[ℝ] ℝ × E ↦ A (X σ.1.1))
      (p.update_comp_left e.toContinuousLinearMap L u).symm
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  convert ht using 1
  ext u
  rw [mem_slice]
  change
    ((e (p.update L u (X σ.1.1))).1,
      P σ.1.1 (e (p.update L u (X σ.1.1))).2 + P σ.1.1 (Q σ.1.1 σ.1.2.2)) ≠ 0 ↔
      planarProjectorSymbol z (p.update φ (e u) (X σ.1.1)) + c ≠ 0
  rw [hupdate, hzP, hzP, ← add_smul]
  simp [planarProjectorSymbol_apply, c, smul_eq_zero, hz0]

end NativeRelation

#print axioms contMDiff_planarProjectorJetValue
#print axioms isOpen_planarProjectorJetRelation
#print axioms ample_planarProjectorJetRelation

end GlobalEmbedding.Paper
