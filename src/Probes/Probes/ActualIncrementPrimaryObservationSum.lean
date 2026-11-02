import Probes.ActualIncrementPrimaryGlobalSupport
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-! Genuine primary observation sums use the active primary and subordinate
counts, never either total finite cardinality. Relative support suffices even
when the ambient parameter domain has a boundary. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

/-- True active primary/subordinate cardinality. -/
theorem actual_primary_active_pair_card_le
    {Label Sub P : Type*} [Fintype Label] [Fintype Sub]
    (K : Label → Set P) (Ksub : Label → Sub → Set P)
    (hsub : ∀ nu a, Ksub nu a ⊆ K nu) (x : P) (L R : ℕ)
    (hL : (Finset.univ.filter (fun nu => x ∈ K nu)).card ≤ L)
    (hR : ∀ nu, (Finset.univ.filter (fun a => x ∈ Ksub nu a)).card ≤ R) :
    (Finset.univ.filter (fun p : Label × Sub => x ∈ Ksub p.1 p.2)).card ≤ L*R := by
  let active := Finset.univ.filter (fun nu => x ∈ K nu)
  let pieces := fun nu => ({nu} : Finset Label).product
    (Finset.univ.filter (fun a => x ∈ Ksub nu a))
  have hs : (Finset.univ.filter (fun p : Label × Sub => x ∈ Ksub p.1 p.2)) ⊆
      active.biUnion pieces := by
    intro p hp
    have hx := (Finset.mem_filter.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub p.1 p.2 hx⟩, ?_⟩
    exact Finset.mem_product.mpr ⟨by simp, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
  have hp : ∀ nu ∈ active, (pieces nu).card ≤ R := by
    intro nu _
    simpa only [pieces,Finset.product_eq_sprod,Finset.card_product,Finset.card_singleton,one_mul]
      using hR nu
  exact (Finset.card_le_card hs).trans
    ((Finset.card_biUnion_le_card_mul active pieces R hp).trans (Nat.mul_le_mul_right R hL))

/-- Native joint fast jets of the literal double sum after genuine observation
pullback. Inactive terms have zero germs, including chart boundaries. -/
theorem actual_primary_observation_sum_weighted_jets
    {Label Sub X P V : Type*} [Fintype Label] [Fintype Sub]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (waves : Label → Sub → P → V) (K : Label → Set P) (Ksub : Label → Sub → Set P)
    (hsub : ∀ nu a, Ksub nu a ⊆ K nu)
    (W : Set P) (hW : IsOpen W)
    (hsupport : ∀ nu a, tsupport (fun y : W => waves nu a y) ⊆ Subtype.val ⁻¹' Ksub nu a)
    (kappa : X → P) (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Sub → Set X) (hO : ∀ nu a, IsOpen (O nu a))
    (hSO : ∀ nu a, Omega ∩ kappa ⁻¹' Ksub nu a ⊆ O nu a)
    (hreg : ∀ nu a, ContDiffOn ℝ ∞ (waves nu a ∘ kappa) (O nu a))
    (L R j : ℕ)
    (hL : ∀ x ∈ S, (Finset.univ.filter (fun nu => kappa x ∈ K nu)).card ≤ L)
    (hR : ∀ nu, ∀ x ∈ S, (Finset.univ.filter (fun a => kappa x ∈ Ksub nu a)).card ≤ R)
    (tau Budget : ℝ) (htau : 0 < tau) (hBudget : 0 ≤ Budget)
    (hbound : ∀ nu a, ∀ k ≤ j, ∀ x ∈ S ∩ kappa ⁻¹' Ksub nu a,
      tau^k * ‖iteratedFDeriv ℝ k (waves nu a ∘ kappa) x‖ ≤ Budget) :
    ContDiffOn ℝ ∞ (fun y => ∑ nu, ∑ a, waves nu a (kappa y)) Omega ∧
      ∀ k ≤ j, ∀ x ∈ S,
      tau^k * ‖iteratedFDeriv ℝ k (fun y => ∑ nu, ∑ a, waves nu a (kappa y)) x‖ ≤
        (L*R : ℕ)*Budget := by
  let f : Label × Sub → P → V := fun p y => waves p.1 p.2 y
  have hactive : ∀ x ∈ S,
      (Finset.univ.filter (fun p : Label × Sub => kappa x ∈ Ksub p.1 p.2)).card ≤ L*R :=
    fun x hx => actual_primary_active_pair_card_le K Ksub hsub (kappa x) L R
      (hL x hx) (fun nu => hR nu x hx)
  have hh := parameterRound2_relative_supported_sum_weighted_jets f W
    (fun p : Label × Sub => Ksub p.1 p.2) hW (fun p => hsupport p.1 p.2)
    kappa Omega S hOmega hSOmega hkappa hmap (fun p => O p.1 p.2) (fun p => hO p.1 p.2)
    (fun p => hSO p.1 p.2) (fun p => hreg p.1 p.2) (L*R) j 0 hactive tau Budget htau hBudget
    (fun p k hk x hx => by simpa only [Nat.add_zero] using hbound p.1 p.2 k hk x hx)
  simpa only [Fintype.sum_prod_type,f,Nat.add_zero] using hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_active_pair_card_le
#print axioms GlobalEmbedding.Continuation.actual_primary_observation_sum_weighted_jets
