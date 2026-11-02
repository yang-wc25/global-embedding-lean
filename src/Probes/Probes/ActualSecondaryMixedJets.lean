import Smoothing.ParameterGeometryJets

/-!
# Native mixed derivatives of the actual secondary map

The joint secondary estimates apply to native parameter derivatives AFTER
the native spatial first derivative or Hessian. This file proves the
restriction identities and norm bounds, rather than interchanging two
unproved totalized derivatives. Each restriction is the fixed native `inl`
or `inr` map of norm at most one, so no dimension-dependent conversion is
silently treated as an isometry.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- These are the native operator structures, named locally only to avoid
-- repeated deep typeclass synthesis; no norm or resource limit is changed.
private noncomputable local instance secondarySpatialBilinearSemi :
    SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance secondarySpatialBilinearNormed :
    NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance secondarySpatialBilinearSpace :
    NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance secondaryParameterHessianSemi :
    SeminormedAddCommGroup (Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance secondaryParameterHessianNormed :
    NormedAddCommGroup (Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance secondaryParameterHessianSpace :
    NormedSpace ℝ (Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance secondaryTwoParameterHessianSemi :
    SeminormedAddCommGroup (Ep →L[ℝ] Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance secondaryTwoParameterHessianNormed :
    NormedAddCommGroup (Ep →L[ℝ] Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The first actual parameter derivative is the restriction of the genuine
joint derivative to `inl`. Its entire joint field is smooth on the same open
set; no global extension of the input family is assumed. -/
theorem actual_joint_parameter_first_bridge
    (f : Ep × Es → Y) (O : Set (Ep × Es)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) :
    (∀ z ∈ O, fderiv ℝ (fun p => f (p, z.2)) z.1 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ Ep Es)) ∧
      ContDiffOn ℝ ∞ (fun z : Ep × Es => fderiv ℝ (fun p => f (p, z.2)) z.1) O := by
  have he (z : Ep × Es) (hz : z ∈ O) :
      fderiv ℝ (fun p => f (p, z.2)) z.1 =
        (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ Ep Es) := by
    have hd := (hf.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)).fderiv
  refine ⟨he, ?_⟩
  let P : ((Ep × Es) →L[ℝ] Y) →L[ℝ] (Ep →L[ℝ] Y) :=
    (ContinuousLinearMap.compL ℝ Ep (Ep × Es) Y).flip (ContinuousLinearMap.inl ℝ Ep Es)
  exact (P.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hO (m := ∞) (by simp))).congr he

/-- Every additional joint derivative of the actual parameter-derivative
field is bounded by one higher derivative of the same joint map. -/
theorem actual_parameter_first_jet_le
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Ep × Es => fderiv ℝ (fun p => f (p, y.2)) y.1) z‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) f z‖ := by
  let P : ((Ep × Es) →L[ℝ] Y) →L[ℝ] (Ep →L[ℝ] Y) :=
    (ContinuousLinearMap.compL ℝ Ep (Ep × Es) Y).flip (ContinuousLinearMap.inl ℝ Ep Es)
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro L
    change ‖L.comp (ContinuousLinearMap.inl ℝ Ep Es)‖ ≤ 1 * ‖L‖
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ) (E := Ep) (F := Es)) (norm_nonneg L))
  have he : (fun y : Ep × Es => fderiv ℝ (fun p => f (p, y.2)) y.1)
      =ᶠ[𝓝 z] P ∘ fderiv ℝ f := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact (actual_joint_parameter_first_bridge f O hO hf).1 y hy
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have hd := hf.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hb := P.norm_iteratedFDeriv_comp_left (hd.contDiffAt (hO.mem_nhds hz))
    (n := k) (by simp)
  apply hb.trans
  rw [← norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (norm_nonneg _)

/-- First parameter response after the actual spatial first derivative;
the right side is a derivative of the SAME map. -/
theorem actual_parameter_spatial_first_jet_le
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Ep × Es =>
      fderiv ℝ (fun p => fderiv ℝ (fun x => f (p, x)) y.2) y.1) z‖ ≤
      ‖iteratedFDeriv ℝ (k + 2) f z‖ := by
  have hg := (incrementsJointSpatialJets_bridge f O hO hf).2.1
  exact (actual_parameter_first_jet_le hO hg hz k).trans (spatial_first_jet_le hO hf hz (k + 1))

/-- First parameter response after the actual spatial Hessian. All additional
joint directions are retained; the total cost is precisely three derivatives. -/
theorem actual_parameter_spatial_hessian_jet_le
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Ep × Es =>
      fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ (fun x => f (p, x))) y.2) y.1) z‖ ≤
      ‖iteratedFDeriv ℝ (k + 3) f z‖ := by
  have hg := (incrementsJointSpatialJets_bridge f O hO hf).2.2
  exact (actual_parameter_first_jet_le hO hg hz k).trans (spatial_second_jet_le hO hf hz (k + 1))

/-- The native first parameter derivative of the native spatial Hessian is
bounded in operator norm by the total third derivative, with constant one. -/
theorem actual_parameter_spatial_hessian_norm_le
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) :
    ‖fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ (fun x => f (p, x))) z.2) z.1‖ ≤
      ‖iteratedFDeriv ℝ 3 f z‖ := by
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using
    actual_parameter_spatial_hessian_jet_le hO hf hz 0

/-- Second native parameter derivative after the spatial Hessian is likewise
a norm-one restriction of total fourth-order data. This is useful for the
even background-response estimate at the origin. -/
theorem actual_parameter_two_spatial_hessian_norm_le
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) :
    ‖fderiv ℝ (fderiv ℝ
      (fun p => fderiv ℝ (fderiv ℝ (fun x => f (p, x))) z.2)) z.1‖ ≤
      ‖iteratedFDeriv ℝ 4 f z‖ := by
  let g := fun y : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (y.1, x))) y.2
  have hg : ContDiffOn ℝ ∞ g O := (incrementsJointSpatialJets_bridge f O hO hf).2.2
  have hpg := (actual_joint_parameter_first_bridge g O hO hg).2
  have h1 := actual_parameter_first_jet_le hO hpg hz 0
  have h2 := actual_parameter_first_jet_le hO hg hz 1
  have h3 := spatial_second_jet_le hO hf hz 2
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using h1.trans (h2.trans h3)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_parameter_first_jet_le
#print axioms GlobalEmbedding.Continuation.actual_parameter_spatial_hessian_norm_le
#print axioms GlobalEmbedding.Continuation.actual_parameter_two_spatial_hessian_norm_le
