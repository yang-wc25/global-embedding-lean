import Smoothing.ParameterRound2IdentityParameter

/-! The original identity parameter chart has the exact full joint identity
map. Its positive jets have a scale-independent bound, in every parameter
dimension, including nonzero dimensions and arbitrary compact parameter sets. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
namespace GlobalEmbedding.Continuation

theorem parameterRound2_identity_parameter_map_jets (m d : ℕ)
    (ell : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))) :
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (parameterRound2_meanParameterMap (m := m)
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin d)))) z‖ ≤ 1 := by
  rw [parameterRound2_identity_parameter_map]
  let X := EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))
  change ell^(k-1)*‖iteratedFDeriv ℝ k (ContinuousLinearMap.id ℝ X) z‖ ≤ 1
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  cases r with
  | zero =>
    simp only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
    exact ContinuousLinearMap.norm_id_le
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (ContinuousLinearMap.id ℝ X) = fun _ : X => ContinuousLinearMap.id ℝ X :=
      funext (fun y => (ContinuousLinearMap.id ℝ X).fderiv)
    rw [he,iteratedFDeriv_const_of_ne (by omega : r+1 ≠ 0)]
    simp

#print axioms parameterRound2_identity_parameter_map_jets
end GlobalEmbedding.Continuation
