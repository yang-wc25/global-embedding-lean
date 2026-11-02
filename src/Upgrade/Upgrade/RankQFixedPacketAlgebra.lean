import GlobalEmbedding.Paper.UpgradeRankQDuplicatedPrincipalPacket

/-!
# The accepted duplicated-principal algebra with the correct quantifier order

This is the internal `hcore` and its scalar identities extracted verbatim
(up to indentation and declaration arguments) from the frozen master file
`UpgradeRankQDuplicatedPrincipalPacket.lean`. That theorem chooses its local
waves before using the weights, but its public statement quantified weights
first. Here the fixed actual packet can be given to probes and the returned
positive unequal weights can subsequently be consumed without reselecting
any phase, field, support, or tensor. No bottom-level rank classification is
reproved; the source-level extraction is recorded in reports/rank_q.md.
-/

noncomputable section
open Module Function
open scoped BigOperators
namespace GlobalEmbedding.Upgrade

/-- The already accepted algebra for a fixed packet, for every later choice
of positive unequal weights. `Rw1` is the original fixed packet response. -/
theorem rankQFixedPacket_duplicated_span {n : ℕ} (hn : 0 < n)
    (K1 L1 : Type*) [NormedAddCommGroup K1] [NormedSpace ℝ K1]
    [FiniteDimensional ℝ K1] [NormedAddCommGroup L1] [NormedSpace ℝ L1]
    [FiniteDimensional ℝ L1]
    (D : Fin n → K1 →L[ℝ] L1) (ell : Fin n → L1)
    (Rw1 : (Fin n → ℝ) → (K1 →L[ℝ] L1))
    (hdK : finrank ℝ K1 = n) (hdL : finrank ℝ L1 = 1)
    (hDkill : ∀ i, ell i = 0 → D i = 0)
    (hRform : ∀ t, Rw1 t = ∑ i, t i • D i)
    (hRonto : Function.Surjective (fderiv ℝ Rw1 0))
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let J (ij : Fin n × Fin 2) :=
      (D ij.1, -((lambda ij.1 ij.2 ^ 2)⁻¹) • ell ij.1)
    Submodule.span ℝ (Set.range J) = ⊤ ∧
      finrank ℝ (Submodule.span ℝ (Set.range J)) = n + 1 := by
  classical
  let c (i : Fin n) (j : Fin 2) : ℝ := (lambda i j ^ 2)⁻¹
  let delta (i : Fin n) := c i 0 - c i 1
  have hd (i : Fin n) : delta i ≠ 0 := by
    intro hz
    have he : c i 0 = c i 1 := sub_eq_zero.mp hz
    have hs : lambda i 0 ^ 2 = lambda i 1 ^ 2 := inv_inj.mp he
    apply hne i
    exact (sq_eq_sq₀ (hlambda i 0).le (hlambda i 1).le).mp hs
  have hs0 (i : Fin n) : -(c i 1) / delta i + c i 0 / delta i = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        rw [sub_div, neg_div, sub_eq_add_neg, add_comm]
      _ = 1 := div_self (hd i)
  have hs1 (i : Fin n) :
      (-(c i 1) / delta i) * -(c i 0) + (c i 0 / delta i) * -(c i 1) = 0 := by
    ring
  have hs2 (i : Fin n) : (-1 / delta i : ℝ) + 1 / delta i = 0 := by
    rw [neg_div, neg_add_cancel]
  have hs3 (i : Fin n) :
      (-1 / delta i) * -(c i 0) + (1 / delta i) * -(c i 1) = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        ring
      _ = 1 := div_self (hd i)
  have hm0 (w : K1 →L[ℝ] L1) (i : Fin n) :
      (-(c i 1) / delta i) • w + (c i 0 / delta i) • w = w := by
    rw [← add_smul, hs0 i, one_smul]
  have hm1 (w : L1) (i : Fin n) :
      (-(c i 1) / delta i) • (-(c i 0) • w) +
        (c i 0 / delta i) • (-(c i 1) • w) = 0 := by
    rw [smul_smul, smul_smul, ← add_smul, hs1 i, zero_smul]
  have hm2 (w : K1 →L[ℝ] L1) (i : Fin n) :
      (-1 / delta i) • w + (1 / delta i) • w = 0 := by
    rw [← add_smul, hs2 i, zero_smul]
  have hm3 (w : L1) (i : Fin n) :
      (-1 / delta i) • (-(c i 0) • w) + (1 / delta i) • (-(c i 1) • w) = w := by
    rw [smul_smul, smul_smul, ← add_smul, hs3 i, one_smul]
  let T : (Fin n → ℝ) →L[ℝ] (K1 →L[ℝ] L1) :=
    LinearMap.toContinuousLinearMap (Fintype.linearCombination ℝ D)
  have hTt (t : Fin n → ℝ) : T.toLinearMap.toFun t = ∑ i, t i • D i :=
    Fintype.linearCombination_apply ℝ D t
  have hRfun : Rw1 = T.toLinearMap.toFun := funext fun t ↦ (hRform t).trans (hTt t).symm
  have hTonto : Function.Surjective T.toLinearMap.toFun := by
    have hf : fderiv ℝ Rw1 0 = T :=
      (congrArg (fun f : (Fin n → ℝ) → (K1 →L[ℝ] L1) ↦ fderiv ℝ f 0) hRfun).trans
        (ContinuousLinearMap.fderiv (𝕜 := ℝ) (E := Fin n → ℝ)
          (F := K1 →L[ℝ] L1) (x := (0 : Fin n → ℝ)) T)
    intro Y
    obtain ⟨t, ht⟩ := hRonto Y
    exact ⟨t, (DFunLike.congr_fun hf t).symm.trans ht⟩
  have hDspan : Submodule.span ℝ (Set.range D) = ⊤ :=
    (Fintype.range_linearCombination ℝ D).symm.trans (LinearMap.range_eq_top.mpr hTonto)
  have hdHom : finrank ℝ (K1 →L[ℝ] L1) = n := by
    calc
      _ = finrank ℝ (K1 →ₗ[ℝ] L1) :=
        (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := K1) (F' := L1)).finrank_eq.symm
      _ = finrank ℝ K1 * finrank ℝ L1 := Module.finrank_linearMap ℝ ℝ K1 L1
      _ = n := by rw [hdK, hdL, mul_one]
  have hell : ∃ i, ell i ≠ 0 := by
    by_contra h
    have hall : ∀ i, ell i = 0 := by simpa only [not_exists, not_not] using h
    have hDzero (i : Fin n) : D i = 0 := hDkill i (hall i)
    have hbot : Submodule.span ℝ (Set.range D) = ⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro _ ⟨i, rfl⟩
      exact hDzero i
    have heq : (⊤ : Submodule ℝ (K1 →L[ℝ] L1)) = ⊥ := hDspan.symm.trans hbot
    have hz := congrArg (fun S : Submodule ℝ (K1 →L[ℝ] L1) ↦ finrank ℝ S) heq
    rw [finrank_top, finrank_bot, hdHom] at hz
    exact (by omega : n ≠ 0) hz
  have hellspan : Submodule.span ℝ (Set.range ell) = ⊤ := by
    obtain ⟨i, hi⟩ := hell
    have hsingle : Submodule.span ℝ ({ell i} : Set L1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq ((finrank_span_singleton hi).trans hdL.symm)
    apply top_unique
    rw [← hsingle]
    apply Submodule.span_mono
    intro v hv
    exact ⟨i, Set.mem_singleton_iff.mp hv |>.symm⟩
  let J (ij : Fin n × Fin 2) : (K1 →L[ℝ] L1) × L1 :=
    (D ij.1, -(c ij.1 ij.2) • ell ij.1)
  let Z := Submodule.span ℝ (Set.range J)
  have hZB (i : Fin n) : (D i, (0 : L1)) ∈ Z := by
    have he : (-(c i 1) / delta i) • J (i, 0) +
        (c i 0 / delta i) • J (i, 1) = (D i, 0) := by
      exact Prod.ext (hm0 (D i) i) (hm1 (ell i) i)
    rw [← he]
    exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
      (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))
  have hZV (i : Fin n) : ((0 : K1 →L[ℝ] L1), ell i) ∈ Z := by
    have he : (-1 / delta i) • J (i, 0) + (1 / delta i) • J (i, 1) = (0, ell i) := by
      exact Prod.ext (hm2 (D i) i) (hm3 (ell i) i)
    rw [← he]
    exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
      (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))
  have hleft : Submodule.span ℝ (Set.range D) ≤
      Z.comap (LinearMap.inl ℝ (K1 →L[ℝ] L1) L1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hZB i
  have hright : Submodule.span ℝ (Set.range ell) ≤
      Z.comap (LinearMap.inr ℝ (K1 →L[ℝ] L1) L1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hZV i
  have hZ : Z = ⊤ := by
    apply top_unique
    intro p hp
    have hB : (p.1, (0 : L1)) ∈ Z := hleft (by rw [hDspan]; trivial)
    have hV : ((0 : K1 →L[ℝ] L1), p.2) ∈ Z := hright (by rw [hellspan]; trivial)
    have he : (p.1, (0 : L1)) + ((0 : K1 →L[ℝ] L1), p.2) = p :=
      Prod.ext (add_zero p.1) (zero_add p.2)
    exact he ▸ Z.add_mem hB hV
  have hdimZ : finrank ℝ Z = n + 1 := by
    rw [hZ, finrank_top, Module.finrank_prod, hdHom, hdL]
  exact ⟨hZ, hdimZ⟩

end GlobalEmbedding.Upgrade
