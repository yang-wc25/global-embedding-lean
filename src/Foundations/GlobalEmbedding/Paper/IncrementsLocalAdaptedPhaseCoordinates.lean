import GlobalEmbedding.Paper.RegularLevelLocalGraph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-!
# Stage 2: the ORIGINAL parameter-preserving adapted phase coordinates

Source: main.tex594–609,617–650, lem:increments. Exclusive worker W5 child5A.
Statement ONLY for ROOT lock, with one expected named proof hole.
W2 alone owns fixed-parameter slices and maximal-atlas membership (child5B).
-/

open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- A genuinely noncritical ORIGINAL spatial phase gives a local joint chart
preserving the SAME parameter and the literal phase as distinguished coordinate.
Smoothness and inverse identities hold only on the actual open chart domains;
the source lies in the ORIGINAL open input domain. No global extension is used.

Source: main.tex594–609,617–650, adapted coordinates for the actual finite-mode
construction with finite auxiliary parameters.

Natural-language proof, pending ROOT exact statement lock: apply native
HasStrictFDerivAt.implicitToOpenPartialHomeomorph to the ORIGINAL augmented map
(p,x) -> (p,psi(p,x)). Its actual derivative is surjective because the original
spatial scalar derivative is nonzero; spatial adjustment supplies the scalar
component independently of the parameter component. The native constructor
preserves (p,psi) exactly as its first output. Its actual derivative kernel has
the original transverse dimension m. Use fixed native finite-dimensional linear
coordinates on that kernel and product reassociation to obtain the SAME spatial
Euclidean model, preserving the first scalar coordinate literally (not shifted
by psi at the base). No isometry or norm-one claim is made for that conversion.
Reuse the existing RegularLevelLocalGraph smooth inverse restriction prefix:
shrink inside the original W and the open locus of invertible full derivative,
then use native OpenPartialHomeomorph.contDiffAt_symm at each target point.
Do not use restrContDiff at infinity, which its hypotheses explicitly exclude.
The original base remains in the source. Native partial inverse laws give the
parameter and phase identities on the actual target. This produces ONE joint
chart only; W2 constructs its actual spatial slices and atlas membership.

No derivative-surjectivity, invertible-Jacobian, desired chart or coordinate
identity is an input premise. Arbitrary finite-dimensional parameters, including
dimension zero, and m=0 (one spatial coordinate) are allowed. Spatial dimension
zero cannot satisfy the original noncriticality assumption. No compactness,
whole-parameter smooth extension, quantitative radius/count or full original
admissibility/profile assertion is added. -/
theorem increments_exists_local_adapted_phase_coordinates
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [FiniteDimensional ℝ Ep] {m : ℕ}
    (ψ : Ep × EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (W : Set (Ep × EuclideanSpace ℝ (Fin (m + 1)))) (_hW : IsOpen W)
    (z₀ : Ep × EuclideanSpace ℝ (Fin (m + 1))) (_hz₀ : z₀ ∈ W)
    (_hψ : ContDiffOn ℝ ∞ ψ W)
    (_hcritical : fderiv ℝ (fun x ↦ ψ (z₀.1, x)) z₀.2 ≠ 0) :
    ∃ a : OpenPartialHomeomorph
        (Ep × EuclideanSpace ℝ (Fin (m + 1)))
        (Ep × EuclideanSpace ℝ (Fin (m + 1))),
      z₀ ∈ a.source ∧ a.source ⊆ W ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = ψ z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ ψ (a.symm z) = z.2 0) := by
  classical
  let D := EuclideanSpace ℝ (Fin (m + 1))
  have : CompleteSpace Ep := FiniteDimensional.complete ℝ Ep
  have hψ₀ : ContDiffAt ℝ ∞ ψ z₀ := _hψ.contDiffAt (_hW.mem_nhds _hz₀)
  let d := fderiv ℝ ψ z₀
  let ell : D →L[ℝ] ℝ := d.comp (ContinuousLinearMap.inr ℝ Ep D)
  have hslice := (incrementsJointSpatialJets_bridge ψ W _hW _hψ).1 z₀ _hz₀
  have hell : ell ≠ 0 := by
    simpa only [hslice] using _hcritical
  obtain ⟨v, hv⟩ : ∃ v : D, ell v ≠ 0 := by
    by_contra! h
    apply hell
    ext v
    exact h v
  have hellonto : Function.Surjective ell := by
    intro t
    refine ⟨(t / ell v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ t hv
  let g : Ep × D → Ep × ℝ := fun z ↦ (z.1, ψ z)
  let L : (Ep × D) →L[ℝ] (Ep × ℝ) := (ContinuousLinearMap.fst ℝ Ep D).prod d
  have hLonto : Function.Surjective L := by
    rintro ⟨p, t⟩
    obtain ⟨x, hx⟩ := hellonto (t - d (p, 0))
    refine ⟨(p, x), Prod.ext rfl ?_⟩
    change d (p, x) = t
    have he : (p, x) = (p, (0 : D)) + ((0 : Ep), x) := by simp
    rw [he, map_add]
    change d (p, 0) + ell x = t
    rw [hx]
    ring
  have hrange : L.range = ⊤ := LinearMap.range_eq_top.mpr hLonto
  have hdg : HasStrictFDerivAt g L z₀ :=
    hasStrictFDerivAt_fst.prodMk (hψ₀.hasStrictFDerivAt (by simp))
  let hker := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hdg.implicitFunctionDataOfComplemented g L hrange hker
  let T := φ.prodFun
  let e₀ := hdg.implicitToOpenPartialHomeomorph g L hrange
  have hT : ContDiffOn ℝ ∞ T W := by
    change ContDiffOn ℝ ∞ (fun z ↦ (g z, (Classical.choose hker) (z - z₀))) W
    exact (contDiffOn_fst.prodMk _hψ).prodMk
      (((Classical.choose hker).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hT₀ : ContDiffAt ℝ ∞ T z₀ := hT.contDiffAt (_hW.mem_nhds _hz₀)
  have hgood : ∀ᶠ z in 𝓝 z₀, (fderiv ℝ T z).IsInvertible :=
    hT₀.continuousAt_fderiv (by simp) φ.isInvertible_fderiv_prodFun.eventually_nhds
  have hbase : z₀ ∈ e₀.source := hdg.mem_implicitToOpenPartialHomeomorph_source hrange
  have hnhds : {z | z ∈ W ∧ z ∈ e₀.source ∧ (fderiv ℝ T z).IsInvertible} ∈
      𝓝 z₀ :=
    Filter.inter_mem (_hW.mem_nhds _hz₀)
      (Filter.inter_mem (e₀.open_source.mem_nhds hbase) hgood)
  obtain ⟨S, hSsub, hSopen, hzS⟩ := mem_nhds_iff.mp hnhds
  let er := e₀.restrOpen S hSopen
  have hEr : ContDiffOn ℝ ∞ er er.source :=
    hT.mono (fun z hz ↦ (hSsub hz.2).1)
  have hEri : ContDiffOn ℝ ∞ er.symm er.target := by
    intro y hy
    have hys := hSsub (er.map_target hy).2
    have hTy := hT.contDiffAt (_hW.mem_nhds hys.1)
    obtain ⟨A, hA⟩ := hys.2.2
    have hd : HasFDerivAt T (A : (Ep × D) →L[ℝ] ((Ep × ℝ) × L.ker)) (er.symm y) := by
      rw [hA]
      exact (hTy.differentiableAt (by simp)).hasFDerivAt
    exact (er.contDiffAt_symm hy hd hTy).contDiffWithinAt
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  have hD : Module.finrank ℝ D = m + 1 := by simp [D]
  have hdimK : Module.finrank ℝ L.ker = m := by
    simp only [Module.finrank_prod, Module.finrank_self, hD] at hdim
    omega
  let kcoord : L.ker ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdimK)
  let spcoord : (ℝ × L.ker) ≃L[ℝ] D :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr kcoord).trans
      ((Fin.consEquivL ℝ (fun _ : Fin (m + 1) ↦ ℝ)).trans
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm)
  let C : ((Ep × ℝ) × L.ker) ≃L[ℝ] (Ep × D) :=
    (ContinuousLinearEquiv.prodAssoc ℝ Ep ℝ L.ker).trans
      ((ContinuousLinearEquiv.refl ℝ Ep).prodCongr spcoord)
  have hCfst (q : (Ep × ℝ) × L.ker) : (C q).1 = q.1.1 := rfl
  have hCzero (q : (Ep × ℝ) × L.ker) : (C q).2 0 = q.1.2 := rfl
  let a := er.trans C.toHomeomorph.toOpenPartialHomeomorph
  have hzEr : z₀ ∈ er.source := ⟨hbase, hzS⟩
  have hforward (z : Ep × D) (_hz : z ∈ a.source) :
      (a z).1 = z.1 ∧ (a z).2 0 = ψ z := by
    change (C (er z)).1 = z.1 ∧ (C (er z)).2 0 = ψ z
    rw [hCfst, hCzero]
    change (e₀ z).1.1 = z.1 ∧ (e₀ z).1.2 = ψ z
    rw [hdg.implicitToOpenPartialHomeomorph_fst hrange]
    exact ⟨rfl, rfl⟩
  refine ⟨a, ⟨hzEr, Set.mem_univ _⟩, ?_, ?_, ?_, hforward, ?_⟩
  · intro z hz
    exact (hSsub hz.1.2).1
  · exact C.contDiff.comp_contDiffOn (hEr.mono (fun _ hz ↦ hz.1))
  · exact hEri.comp C.symm.contDiff.contDiffOn (fun _ hz ↦ hz.2)
  · intro z hz
    have h := hforward (a.symm z) (a.map_target hz)
    rw [a.right_inv hz] at h
    exact ⟨h.1.symm, h.2.symm⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.increments_exists_local_adapted_phase_coordinates
