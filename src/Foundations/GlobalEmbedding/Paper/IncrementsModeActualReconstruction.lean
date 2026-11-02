import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame
import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder

/-!
# The actual original homogeneous reconstruction correction

Source: `main.tex`, lem:increments617–650. W5 sole bounded R producer.
The original tangent Gram reconstruction and SAME actual normal J are reused.
W2 owns geometry regularity, W4 actual finite u, W1 the full primary error.
Geometry jet inputs below concern literal original coefficient fields, never a
desired R/error/mean bound. No new section, inverse or derivative carrier is used.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P

/-- Literal original h=0 correction R(u)=dF(g^-1u)+JT(u), in the original ambient
fiber. The actual totalized Gram inverse and actual T are the accepted ones. -/
def incrementsModeReconstruction (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D) (x : D) : V :=
  freeGramRightInverse (fderiv ℝ (F ∘ c) x) (u x) +
    (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseTensor F c u x) : V)

/-- Actual value coefficient of the SAME original reconstruction, not a supplied
bounded operator. The normal inclusion is literal and J is the canonical J. -/
def incrementsModeReconstructionR0 (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) : D →L[ℝ] V :=
  freeGramRightInverse (fderiv ℝ (F ∘ c) x) +
    ((normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)).comp (incrementsModeTransverseValue F c x)

/-- Actual first-jet coefficient of the SAME original reconstruction. The
original transverse symmetrization and its factor one half are retained. -/
def incrementsModeReconstructionR1 (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) : (D →L[ℝ] D) →L[ℝ] V :=
  ((normalSpace (I := I) F (c x)).subtypeL.comp
    (incrementsModeCoordinateJ F hF c x)).comp incrementsModeTransverseJet

/-- The original correction is literally R0(x)u+R1(x)Du. Only the accepted actual
T split and native linear-map additivity are needed, including degenerate data. -/
theorem incrementsModeReconstruction_split (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D) (x : D) :
    incrementsModeReconstruction F hF c u x =
      incrementsModeReconstructionR0 F hF c x (u x) +
        incrementsModeReconstructionR1 F hF c x (fderiv ℝ u x) := by
  simp only [incrementsModeReconstruction, incrementsModeTransverseTensor_split,
    map_add, Submodule.coe_add, incrementsModeReconstructionR0,
    incrementsModeReconstructionR1, add_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact (add_assoc _ _ _).symm

/-- Rewrite the included SAME J with its sole accepted ambient-frame provider.
No J, inverse or normal model is reconstructed here. -/
theorem incrementsModeReconstruction_ambient (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D) (x : D) :
    incrementsModeReconstruction F hF c u x =
      freeGramRightInverse (fderiv ℝ (F ∘ c) x) (u x) +
        freeGramRightInverse (incrementsModeAmbientTransverseFrame F hF c x)
          (incrementsModeTransverseTensor F c u x) := by
  rw [incrementsModeReconstruction, incrementsModeCoordinateJ_ambient_apply]

omit [TopologicalSpace M] in
/-- Actual T(u) is smooth on the original open domain when its original geometry
coefficient and original u are smooth there. There is no global extension input. -/
theorem incrementsModeTransverseTensor_contDiffOn (F : M → V) (c : D → M)
    (O : Set D) (hO : IsOpen O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (incrementsModeTransverseTensor F c u) O := by
  have hd := hu.fderiv_of_isOpen hO (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  exact ((hT0.clm_apply hu).add (contDiffOn_const.clm_apply hd)).congr
    (fun x _ ↦ incrementsModeTransverseTensor_split F c u x)

/-- Actual R(u) regularity uses only the actual geometry fields on O; W2 derives
these geometry inputs from the original chart, immersion and free hypotheses. -/
theorem incrementsModeReconstruction_contDiffOn (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (O : Set D) (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (incrementsModeReconstruction F hF c u) O := by
  exact (hG.clm_apply hu).add
    (hJ.clm_apply (incrementsModeTransverseTensor_contDiffOn F c O hO hT0 u hu))

/-- Smooth germ subtraction gives actual R(u)-R(v)=R(u-v) on O. This does not
assert linearity of totalized derivatives on arbitrary nonsmooth functions. -/
theorem incrementsModeReconstruction_sub (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (O : Set D) (hO : IsOpen O) (u v : D → D)
    (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O) :
    EqOn (fun x ↦ incrementsModeReconstruction F hF c u x -
      incrementsModeReconstruction F hF c v x)
      (incrementsModeReconstruction F hF c (fun y ↦ u y - v y)) O := by
  intro x hx
  have hu' := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hv' := (hv.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  simp only [incrementsModeReconstruction_split, fderiv_fun_sub hu' hv', map_sub]
  abel

omit [TopologicalSpace M] in
/-- Actual T(u) weighted jets reuse the accepted one-derivative-loss theorem.
Only actual V(x) and native constant symmetrization W are coefficient inputs. -/
theorem incrementsModeTransverseTensor_scaled_jets (F : M → V) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (hu : ContDiffOn ℝ ∞ u O)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M)
    (hT0b : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ M)
    (hub : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u x‖ ≤ K) :
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (incrementsModeTransverseTensor F c u) x‖ ≤
        2 * 2 ^ k * max M ‖incrementsModeTransverseJet (m := m)‖ * K := by
  have hWb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun _ : D ↦ incrementsModeTransverseJet (m := m)) x‖ ≤
        max M ‖incrementsModeTransverseJet (m := m)‖ := by
    intro i _ x _
    by_cases hi : i = 0
    · subst i
      simp
    · rw [iteratedFDeriv_const_of_ne hi]
      simpa using hM.trans (le_max_left M ‖incrementsModeTransverseJet (m := m)‖)
  have hb := increments_first_order_scaled_jet j O S hO hSO
    (fun _ ↦ incrementsModeTransverseJet (m := m)) (incrementsModeTransverseValue F c) u
    contDiffOn_const hT0 hu ell (max M ‖incrementsModeTransverseJet (m := m)‖) K hell hell1 hWb
    (fun i hi x hx ↦ (hT0b i hi x hx).trans (le_max_left _ _)) hub
  have he : incrementsModeTransverseTensor F c u =
      (fun y ↦ incrementsModeTransverseValue F c y (u y) +
        incrementsModeTransverseJet (fderiv ℝ u y)) :=
    funext (incrementsModeTransverseTensor_split F c u)
  rw [he]
  exact hb

/-- Genuine actual reconstruction SIZE from original geometry/input jets.
The same open O and norm set S are retained, with exactly one slow derivative
loss. Neither a desired R bound nor a desired inverse/operator bound is assumed. -/
theorem incrementsModeReconstruction_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (hu : ContDiffOn ℝ ∞ u O)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hGb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ M)
    (hJb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ M)
    (hT0b : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ M)
    (hub : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u x‖ ≤ K) :
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (incrementsModeReconstruction F hF c u) x‖ ≤
        (2 ^ j * M + 2 * 2 ^ (j + j) * M * max M ‖incrementsModeTransverseJet (m := m)‖) * K := by
  have hT := incrementsModeTransverseTensor_contDiffOn F c O hO hT0 u hu
  have hTb := incrementsModeTransverseTensor_scaled_jets F c j O S hO hSO hT0 u hu
    ell M K hell hell1 hM hT0b hub
  have hTb' : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (incrementsModeTransverseTensor F c u) x‖ ≤
        2 * 2 ^ j * max M ‖incrementsModeTransverseJet (m := m)‖ * K := by
    intro i hi x hx
    apply (hTb i hi x hx).trans
    gcongr
    norm_num
  intro k hk x hx
  have h0 := scaled_clm_apply O hO
    (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) u hG hu k 0 ell M K hell.le
    (fun i hi ↦ hGb i (hi.trans hk) x hx)
    (fun i hi ↦ by simpa using hub i (by omega) x hx) (hSO hx)
  have h0' : ell ^ (k + 1) *
      ‖iteratedFDeriv ℝ k (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y) (u y)) x‖ ≤
      2 ^ k * M * K := by
    apply le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hell.le hell1 (by omega : k ≤ k + 1)) (norm_nonneg _))
    simpa using h0
  have h1 := scaled_clm_apply O hO (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) (incrementsModeTransverseTensor F c u) hJ hT
    k 1 ell M (2 * 2 ^ j * max M ‖incrementsModeTransverseJet (m := m)‖ * K) hell.le
    (fun i hi ↦ hJb i (hi.trans hk) x hx)
    (fun i hi ↦ hTb' i (hi.trans hk) x hx) (hSO hx)
  have hsum := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    (((hG.clm_apply hu).of_le (by simp)).contDiffWithinAt (hSO hx))
    (((hJ.clm_apply hT).of_le (by simp)).contDiffWithinAt (hSO hx))
    hO.uniqueDiffOn (hSO hx)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO (hSO hx)] at hsum
  change ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
    (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y) (u y) +
      ((normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) (incrementsModeTransverseTensor F c u y)) x‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ell ^ (k + 1) *
        (‖iteratedFDeriv ℝ k (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y) (u y)) x‖ +
          ‖iteratedFDeriv ℝ k
            (fun y ↦ ((normalSpace (I := I) F (c y)).subtypeL.comp
              (incrementsModeCoordinateJ F hF c y)) (incrementsModeTransverseTensor F c u y)) x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ 2 ^ k * M * K +
        2 ^ k * M * (2 * 2 ^ j * max M ‖incrementsModeTransverseJet (m := m)‖ * K) := by
      nlinarith [h0', h1]
    _ ≤ 2 ^ j * M * K +
        2 ^ j * M * (2 * 2 ^ j * max M ‖incrementsModeTransverseJet (m := m)‖ * K) := by
      gcongr <;> norm_num
    _ = _ := by rw [pow_add]; ring

/-- SAME-input difference has the SAME actual reconstruction constant. The input
bound is on the actual u-v jets, and smoothness justifies every derivative germ. -/
theorem incrementsModeReconstruction_difference_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O) (u v : D → D)
    (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O)
    (ell M Kdiff : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hM : 0 ≤ M) (hKdiff : 0 ≤ Kdiff)
    (hGb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ M)
    (hJb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ M)
    (hT0b : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ M)
    (hdiff : ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ u y - v y) x‖ ≤ Kdiff) :
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsModeReconstruction F hF c u y -
          incrementsModeReconstruction F hF c v y) x‖ ≤
        (2 ^ j * M + 2 * 2 ^ (j + j) * M * max M ‖incrementsModeTransverseJet (m := m)‖) *
          Kdiff := by
  have hb := incrementsModeReconstruction_scaled_jets F hF c j O S hO hSO
    hG hJ hT0 (fun y ↦ u y - v y) (hu.sub hv) ell M Kdiff hell hell1 hM hKdiff
    hGb hJb hT0b hdiff
  intro k hk x hx
  have he := incrementsModeReconstruction_sub F hF c O hO u v hu hv
  have hg : (fun y ↦ incrementsModeReconstruction F hF c u y -
      incrementsModeReconstruction F hF c v y) =ᶠ[𝓝 x]
      incrementsModeReconstruction F hF c (fun y ↦ u y - v y) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact he hy
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb k hk x hx

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction
#print axioms GlobalEmbedding.Paper.incrementsModeReconstructionR0
#print axioms GlobalEmbedding.Paper.incrementsModeReconstructionR1
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_split
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_ambient
#print axioms GlobalEmbedding.Paper.incrementsModeTransverseTensor_contDiffOn
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_contDiffOn
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_sub
#print axioms GlobalEmbedding.Paper.incrementsModeTransverseTensor_scaled_jets
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_scaled_jets
#print axioms GlobalEmbedding.Paper.incrementsModeReconstruction_difference_scaled_jets
