import GlobalEmbedding.Paper.UpgradeRankQDuplicatedPrincipalPacket

/-!
# Reusable extraction of the accepted unequal-weight two-copy identities

The four scalar identities below and their module forms are extracted from
`UpgradeRankQDuplicatedPrincipalPacket.lean` in the frozen master. Making
these identities public allows both incidence consumers to retain the SAME
preselected wave list when probes returns its weights. No differentiated
combination coefficient occurs here: these are pointwise span identities.
-/

noncomputable section
open scoped BigOperators
namespace GlobalEmbedding.Upgrade

variable {ι U V : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V]

/-- The original two-column combinations give both pure components, for the
same fixed columns and every later positive unequal pair of weights. -/
theorem rankQFixedPair_pure_mem
    (A : ι → U) (v : ι → V) (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let J (ij : ι × Fin 2) := (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1)
    ∀ i, (A i, (0 : V)) ∈ Submodule.span ℝ (Set.range J) ∧
      ((0 : U), v i) ∈ Submodule.span ℝ (Set.range J) := by
  let c (i : ι) (j : Fin 2) : ℝ := (lambda i j ^ 2)⁻¹
  let delta (i : ι) := c i 0 - c i 1
  have hd (i : ι) : delta i ≠ 0 := by
    intro hz
    have he : c i 0 = c i 1 := sub_eq_zero.mp hz
    have hs : lambda i 0 ^ 2 = lambda i 1 ^ 2 := inv_inj.mp he
    apply hne i
    exact (sq_eq_sq₀ (hlambda i 0).le (hlambda i 1).le).mp hs
  have hs0 (i : ι) : -(c i 1) / delta i + c i 0 / delta i = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        rw [sub_div, neg_div, sub_eq_add_neg, add_comm]
      _ = 1 := div_self (hd i)
  have hs1 (i : ι) :
      (-(c i 1) / delta i) * -(c i 0) + (c i 0 / delta i) * -(c i 1) = 0 := by
    ring
  have hs2 (i : ι) : (-1 / delta i : ℝ) + 1 / delta i = 0 := by
    rw [neg_div, neg_add_cancel]
  have hs3 (i : ι) :
      (-1 / delta i) * -(c i 0) + (1 / delta i) * -(c i 1) = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        ring
      _ = 1 := div_self (hd i)
  have hm0 (w : U) (i : ι) :
      (-(c i 1) / delta i) • w + (c i 0 / delta i) • w = w := by
    rw [← add_smul, hs0 i, one_smul]
  have hm1 (w : V) (i : ι) :
      (-(c i 1) / delta i) • (-(c i 0) • w) +
        (c i 0 / delta i) • (-(c i 1) • w) = 0 := by
    rw [smul_smul, smul_smul, ← add_smul, hs1 i, zero_smul]
  have hm2 (w : U) (i : ι) :
      (-1 / delta i) • w + (1 / delta i) • w = 0 := by
    rw [← add_smul, hs2 i, zero_smul]
  have hm3 (w : V) (i : ι) :
      (-1 / delta i) • (-(c i 0) • w) + (1 / delta i) • (-(c i 1) • w) = w := by
    rw [smul_smul, smul_smul, ← add_smul, hs3 i, one_smul]
  let J (ij : ι × Fin 2) : U × V := (A ij.1, -(c ij.1 ij.2) • v ij.1)
  let Z := Submodule.span ℝ (Set.range J)
  change ∀ i, (A i, (0 : V)) ∈ Z ∧ ((0 : U), v i) ∈ Z
  intro i
  constructor
  · have he : (-(c i 1) / delta i) • J (i, 0) +
        (c i 0 / delta i) • J (i, 1) = (A i, 0) := by
      exact Prod.ext (hm0 (A i) i) (hm1 (v i) i)
    rw [← he]
    exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
      (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))
  · have he : (-1 / delta i) • J (i, 0) + (1 / delta i) • J (i, 1) = (0, v i) := by
      exact Prod.ext (hm2 (A i) i) (hm3 (v i) i)
    rw [← he]
    exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
      (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))

/-- The span is exactly the product of the two fixed component spans. This
also applies to supported incidence, whose equation and value dimensions
are different from the rank-q case. -/
theorem rankQFixedPair_span_eq
    (A : ι → U) (v : ι → V) (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let J (ij : ι × Fin 2) := (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1)
    Submodule.span ℝ (Set.range J) =
      (Submodule.span ℝ (Set.range A)).prod (Submodule.span ℝ (Set.range v)) := by
  let J (ij : ι × Fin 2) := (A ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • v ij.1)
  let Z := Submodule.span ℝ (Set.range J)
  have hp := rankQFixedPair_pure_mem A v lambda hlambda hne
  have hleft : Submodule.span ℝ (Set.range A) ≤ Z.comap (LinearMap.inl ℝ U V) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (hp i).1
  have hright : Submodule.span ℝ (Set.range v) ≤ Z.comap (LinearMap.inr ℝ U V) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (hp i).2
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    exact ⟨Submodule.subset_span ⟨ij.1, rfl⟩,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij.1, rfl⟩)⟩
  · rintro ⟨a, w⟩ ⟨ha, hw⟩
    have he : (a, (0 : V)) + ((0 : U), w) = (a, w) :=
      Prod.ext (add_zero a) (zero_add w)
    exact he ▸ Z.add_mem (hleft ha) (hright hw)

/-- Transport the same two-copy span through the literal linear value
projection. This is the final `hJvalue`/`hJeq` step of the accepted proof,
kept algebraic so actual quotient norm instances are never unfolded here. -/
theorem rankQFixedPair_projected_span_transfer
    {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (A : ι → U) (v : ι → V) (ell : ι → Z) (Q : V →ₗ[ℝ] Z)
    (hQ : ∀ i, Q (v i) = ell i) (c : ι × Fin 2 → ℝ) (r : ℕ)
    (hspan : Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, c ij • ell ij.1))) = ⊤)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, c ij • ell ij.1)))) = r) :
    Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, Q (c ij • v ij.1)))) = ⊤ ∧
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun ij : ι × Fin 2 ↦ (A ij.1, Q (c ij • v ij.1))))) = r := by
  have heq : (fun ij : ι × Fin 2 ↦ (A ij.1, Q (c ij • v ij.1))) =
      (fun ij : ι × Fin 2 ↦ (A ij.1, c ij • ell ij.1)) := by
    funext ij
    exact Prod.ext rfl ((Q.map_smul (c ij) (v ij.1)).trans (congrArg (fun v ↦ c ij • v) (hQ ij.1)))
  rw [heq]
  exact ⟨hspan, hdim⟩

end GlobalEmbedding.Upgrade
