import NormalPolar.PassiveOriginalObserverFields

/-! The phase is a fixed primitive function. Its actual spatial covector is
differentiated jointly in the new observer, on its true open domain. Compact
active samples produce a common all-order budget before every scale or
background input. This does not assume a completed wave estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M Λ : Type*} [TopologicalSpace M] [Fintype Λ]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem passiveRaw_observer_phase_profiles
    (theta : Λ → Ep × M → ℝ) (host : OpenPartialHomeomorph M D)
    (Omega R : Λ → Set X) (hOmega : ∀ nu, IsOpen (Omega nu))
    (hR : ∀ nu, IsCompact (R nu)) (hRO : ∀ nu, R nu ⊆ Omega nu)
    (hPhase : ∀ nu, ContDiffOn ℝ ∞ (fun z : X => theta nu (z.1,host.symm z.2)) (Omega nu)) :
    (∀ nu, ContDiffOn ℝ ∞
      (fun z : X => fderiv ℝ (fun y => theta nu (z.1,host.symm y)) z.2) (Omega nu)) ∧
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ nu n k, k ≤ n → ∀ z ∈ R nu,
        ∀ r : Fin (m+1), ell^k*‖iteratedFDeriv ℝ k
          (fun w : X => fderiv ℝ (fun y => theta nu (w.1,host.symm y)) w.2
            (EuclideanSpace.single r 1)) z‖ ≤ C n := by
  let gradient := fun nu (z : X) => fderiv ℝ (fun y => theta nu (z.1,host.symm y)) z.2
  have hg : ∀ nu, ContDiffOn ℝ ∞ (gradient nu) (Omega nu) := fun nu =>
    (incrementsJointSpatialJets_bridge (fun z : X => theta nu (z.1,host.symm z.2))
      (Omega nu) (hOmega nu) (hPhase nu)).2.1
  choose C hC hCb using fun nu => exists_compact_native_prefix
    (R nu) (Omega nu) (hR nu) (hOmega nu) (hRO nu) (gradient nu) (hg nu)
  refine ⟨hg,fun n => ∑ nu, C nu n,fun n =>
    Finset.sum_nonneg (fun nu _ => (hC nu n).le),?_⟩
  intro ell hell hell1 nu n k hk z hz r
  have heval := norm_iteratedFDeriv_clm_apply_const
    ((hg nu).contDiffAt ((hOmega nu).mem_nhds (hRO nu hz)))
    (n := k) (c := EuclideanSpace.single r (1:ℝ)) (by simp)
  have hnorm : ‖EuclideanSpace.single r (1:ℝ)‖ = 1 := by simp
  rw [hnorm,one_mul] at heval
  have hb : ell^k*‖iteratedFDeriv ℝ k (gradient nu) z‖ ≤ C nu n :=
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans (hCb nu n k hk z hz)
  have hsum : C nu n ≤ ∑ mu, C mu n := Finset.single_le_sum
    (fun mu _ => (hC mu n).le) (Finset.mem_univ nu)
  exact ((mul_le_mul_of_nonneg_left heval (pow_nonneg hell k)).trans hb).trans hsum

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRaw_observer_phase_profiles
