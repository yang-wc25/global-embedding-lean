import GlobalEmbedding.Paper.IncrementsModeActualReconstruction

/-!
# Original inhomogeneous reconstruction with its actual forcing

Source: `main.tex`, lem:increments617–650. W5 owns only the full Z constructor
and its quantitative consumer. W4 owns the row identities, W2 geometry, W1 E.
The accepted homogeneous R and SAME actual normal J are used without alteration.
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
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

/-- Actual once-sorted transverse selection from the ORIGINAL full source matrix.
Its Pi-to-Euclidean operator norm is retained; it is not asserted to be norm one. -/
def incrementsModeTransverseSourceCLM : Source →L[ℝ] Tdata :=
  (EuclideanSpace.equiv P ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q ↦
      (ContinuousLinearMap.proj q.val.2.succ : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj q.val.1.succ : Source →L[ℝ] (Fin (m + 1) → ℝ)))

/-- The native selector is precisely the existing canonical h_H function. -/
theorem incrementsModeTransverseSource_eq_selector (h : D → Source) (x : D) :
    incrementsModeTransverseSource h x = incrementsModeTransverseSourceCLM (h x) := rfl

/-- The literal original full inhomogeneous displacement, with normal free datum
in the SAME original normalSpace and the original forcing factor minus one half. -/
def incrementsModeFullReconstruction (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D)
    (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) : V :=
  incrementsModeReconstruction F hF c u x + (vf x : V) -
    (1 / 2 : ℝ) • (incrementsModeCoordinateJ F hF c x
      (incrementsModeTransverseSource h x) : V)

/-- Exact W4 row interface: full Z is tangent reconstruction plus the SAME inline
normal vf+JT(u)-Jh_H/2. No new normal field, J or row equation is introduced. -/
theorem incrementsModeFullReconstruction_tangent_normal (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D)
    (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) :
    incrementsModeFullReconstruction F hF c u h vf x =
      freeGramRightInverse (fderiv ℝ (F ∘ c) x) (u x) +
        (vf x + incrementsModeCoordinateJ F hF c x (incrementsModeTransverseTensor F c u x) -
          (1 / 2 : ℝ) • incrementsModeCoordinateJ F hF c x
            (incrementsModeTransverseSource h x) : V) := by
  simp only [incrementsModeFullReconstruction, incrementsModeReconstruction]
  abel

/-- Native full-source selection costs NO derivative. The genuine selector norm
is the only conversion constant, including empty transverse tuples. -/
theorem incrementsModeTransverseSource_scaled_jets
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (h : D → Source) (hh : ContDiffOn ℝ ∞ h O) (ell Kh : ℝ) (hell : 0 ≤ ell)
    (hhb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h x‖ ≤ Kh) :
    ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseSource h) x‖ ≤
        ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh := by
  intro i hi x hx
  have he : incrementsModeTransverseSource h = incrementsModeTransverseSourceCLM ∘ h := rfl
  rw [he]
  calc
    _ ≤ ell ^ i * (‖incrementsModeTransverseSourceCLM (m := m)‖ *
        ‖iteratedFDeriv ℝ i h x‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _
        (hh.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
    _ = ‖incrementsModeTransverseSourceCLM (m := m)‖ *
        (ell ^ i * ‖iteratedFDeriv ℝ i h x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hhb i hi x hx) (norm_nonneg _)

/-- Actual included J times the actual h_H has no additional forcing derivative
loss. No desired forcing/Z estimate or alternative source tensor is an input. -/
theorem incrementsModeForcing_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (h : D → Source) (hh : ContDiffOn ℝ ∞ h O)
    (ell Mg Kh : ℝ) (hell : 0 ≤ ell) (hMg : 0 ≤ Mg) (hKh : 0 ≤ Kh)
    (hJb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hhb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h x‖ ≤ Kh) :
    ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y ↦ (incrementsModeCoordinateJ F hF c y
        (incrementsModeTransverseSource h y) : V)) x‖ ≤
      2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh := by
  have hs : ContDiffOn ℝ ∞ (incrementsModeTransverseSource h) O :=
    incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  have hb := incrementsModeTransverseSource_scaled_jets j O S hO hSO h hh ell Kh hell hhb
  intro k hk x hx
  have hj := scaled_clm_apply O hO
    (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) (incrementsModeTransverseSource h) hJ hs
    k 0 ell Mg (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) hell
    (fun i hi ↦ hJb i (hi.trans hk) x hx)
    (fun i hi ↦ by simpa using hb i (hi.trans hk) x hx) (hSO hx)
  calc
    _ ≤ 2 ^ k * Mg * (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      simpa using hj
    _ ≤ 2 ^ j * Mg * (‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      gcongr
      norm_num
    _ = _ := by ring

/-- Actual full Z smoothness on the original open, from original actual fields.
In particular no global smooth extension of geometry or source is requested. -/
theorem incrementsModeFullReconstruction_contDiffOn (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (O : Set D) (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x))
    (hu : ContDiffOn ℝ ∞ u O) (hh : ContDiffOn ℝ ∞ h O)
    (hvf : ContDiffOn ℝ ∞ (fun x ↦ (vf x : V)) O) :
    ContDiffOn ℝ ∞ (incrementsModeFullReconstruction F hF c u h vf) O := by
  have hs : ContDiffOn ℝ ∞ (incrementsModeTransverseSource h) O :=
    incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  exact ((incrementsModeReconstruction_contDiffOn F hF c O hO hG hJ hT0 u hu).add hvf).sub
    ((hJ.clm_apply hs).const_smul (1 / 2 : ℝ))

/-- Actual full-input difference is full Z of the actual differences on O.
Original geometry is fixed; smooth germs justify the only differential term. -/
theorem incrementsModeFullReconstruction_sub (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (O : Set D) (hO : IsOpen O)
    (u v : D → D) (h g : D → Source)
    (vf vg : (x : D) → normalSpace (I := I) F (c x))
    (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O) :
    EqOn (fun x ↦ incrementsModeFullReconstruction F hF c u h vf x -
      incrementsModeFullReconstruction F hF c v g vg x)
      (incrementsModeFullReconstruction F hF c (fun x ↦ u x - v x)
        (fun x ↦ h x - g x) (fun x ↦ vf x - vg x)) O := by
  intro x hx
  have hr := incrementsModeReconstruction_sub F hF c O hO u v hu hv hx
  simp only [incrementsModeFullReconstruction, incrementsModeTransverseSource_eq_selector,
    map_sub, Submodule.coe_sub, smul_sub]
  rw [← hr]
  module

/-- Real homogeneity of the SAME full inhomogeneous displacement, including
delta zero, at actual smooth u germs. No inverse amplitude or cutoff is used. -/
theorem incrementsModeFullReconstruction_real_smul (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D)
    (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x))
    (δ : ℝ) (x : D) (hu : DifferentiableAt ℝ u x) :
    incrementsModeFullReconstruction F hF c (fun y ↦ δ • u y)
      (fun y ↦ δ • h y) (fun y ↦ δ • vf y) x =
      δ • incrementsModeFullReconstruction F hF c u h vf x := by
  simp only [incrementsModeFullReconstruction, incrementsModeReconstruction_split,
    fderiv_fun_const_smul hu δ, incrementsModeTransverseSource_eq_selector,
    map_smul, Submodule.coe_smul, smul_add, smul_sub]
  rw [smul_comm (1 / 2 : ℝ) δ]

/-- Native locality of the actual full Z: none of u, full h or the free normal
datum can generate displacement outside their original topological supports. -/
theorem incrementsModeFullReconstruction_tsupport (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u : D → D)
    (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x)) :
    tsupport (incrementsModeFullReconstruction F hF c u h vf) ⊆
      tsupport u ∪ (tsupport h ∪ tsupport (fun x ↦ (vf x : V))) := by
  apply closure_minimal _ ((isClosed_tsupport u).union
    ((isClosed_tsupport h).union (isClosed_tsupport (fun x ↦ (vf x : V)))))
  intro x hx
  by_contra hnot
  have hn : x ∉ tsupport u ∧ x ∉ tsupport h ∧
      x ∉ tsupport (fun x ↦ (vf x : V)) := by simpa only [mem_union, not_or] using hnot
  apply hx
  simp only [incrementsModeFullReconstruction, incrementsModeReconstruction_split,
    image_eq_zero_of_notMem_tsupport hn.1, fderiv_of_notMem_tsupport (𝕜 := ℝ) hn.1,
    incrementsModeTransverseSource_eq_selector, image_eq_zero_of_notMem_tsupport hn.2.1,
    image_eq_zero_of_notMem_tsupport hn.2.2, map_zero, Submodule.coe_zero, add_zero,
    smul_zero, sub_zero]

/-- Honest full inhomogeneous SIZE: R consumes one u derivative; forcing and
free-normal data consume only j derivatives. Every field in the input is actual. -/
theorem incrementsModeFullReconstruction_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u : D → D) (h : D → Source) (vf : (x : D) → normalSpace (I := I) F (c x))
    (hu : ContDiffOn ℝ ∞ u O) (hh : ContDiffOn ℝ ∞ h O)
    (hvf : ContDiffOn ℝ ∞ (fun x ↦ (vf x : V)) O)
    (ell Mg Ku Kh Kv : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKu : 0 ≤ Ku) (hKh : 0 ≤ Kh)
    (hGb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mg)
    (hJb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hT0b : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mg)
    (hub : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i u x‖ ≤ Ku)
    (hhb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h x‖ ≤ Kh)
    (hvfb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ (vf y : V)) x‖ ≤ Kv) :
    ∀ k ≤ j, ∀ x ∈ S, ell ^ (k + 1) *
      ‖iteratedFDeriv ℝ k (incrementsModeFullReconstruction F hF c u h vf) x‖ ≤
      (2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
        max Mg ‖incrementsModeTransverseJet (m := m)‖) * Ku +
      ell * (Kv + (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) / 2) := by
  have hR := incrementsModeReconstruction_scaled_jets F hF c j O S hO hSO
    hG hJ hT0 u hu ell Mg Ku hell hell1 hMg hKu hGb hJb hT0b hub
  have hC := incrementsModeForcing_scaled_jets F hF c j O S hO hSO hJ h hh
    ell Mg Kh hell.le hMg hKh hJb hhb
  have hs : ContDiffOn ℝ ∞ (incrementsModeTransverseSource h) O :=
    incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  have hRs := incrementsModeReconstruction_contDiffOn F hF c O hO hG hJ hT0 u hu
  have hCs : ContDiffOn ℝ ∞ (fun y ↦ (incrementsModeCoordinateJ F hF c y
      (incrementsModeTransverseSource h y) : V)) O := hJ.clm_apply hs
  intro k hk x hx
  have hr := (hRs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hv := (hvf.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hc := (hCs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  change ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
    (fun y ↦ incrementsModeReconstruction F hF c u y + (vf y : V) -
      (1 / 2 : ℝ) • (incrementsModeCoordinateJ F hF c y
        (incrementsModeTransverseSource h y) : V)) x‖ ≤ _
  rw [fun_iteratedFDeriv_sub_apply (hr.add hv) (hc.const_smul (1 / 2 : ℝ)),
    fun_iteratedFDeriv_add_apply hr hv, iteratedFDeriv_const_smul_apply' hc]
  calc
    _ ≤ ell ^ (k + 1) *
        (‖iteratedFDeriv ℝ k (incrementsModeReconstruction F hF c u) x‖ +
          ‖iteratedFDeriv ℝ k (fun y ↦ (vf y : V)) x‖ + (1 / 2 : ℝ) *
          ‖iteratedFDeriv ℝ k (fun y ↦ (incrementsModeCoordinateJ F hF c y
            (incrementsModeTransverseSource h y) : V)) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (by
        rw [norm_smul, Real.norm_eq_abs]; norm_num))
    _ = ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (incrementsModeReconstruction F hF c u) x‖ +
        ell * (ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ (vf y : V)) x‖ +
          (ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ (incrementsModeCoordinateJ F hF c y
            (incrementsModeTransverseSource h y) : V)) x‖) / 2) := by rw [pow_succ]; ring
    _ ≤ _ := add_le_add (hR k hk x hx) (mul_le_mul_of_nonneg_left
      (add_le_add (hvfb k hk x hx)
        (div_le_div_of_nonneg_right (hC k hk x hx) (by norm_num))) hell.le)

/-- Honest SAME-input difference of the full displacement. The inputs are actual
u-v, h-g and vf-vg jets; no individual output or prescribed Z difference is used. -/
theorem incrementsModeFullReconstruction_difference_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (u v : D → D) (h g : D → Source)
    (vf vg : (x : D) → normalSpace (I := I) F (c x))
    (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O)
    (hh : ContDiffOn ℝ ∞ h O) (hg : ContDiffOn ℝ ∞ g O)
    (hvf : ContDiffOn ℝ ∞ (fun x ↦ (vf x : V)) O)
    (hvg : ContDiffOn ℝ ∞ (fun x ↦ (vg x : V)) O)
    (ell Mg Ku Kh Kv : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKu : 0 ≤ Ku) (hKh : 0 ≤ Kh)
    (hGb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mg)
    (hJb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mg)
    (hT0b : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mg)
    (hub : ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ u y - v y) x‖ ≤ Ku)
    (hhb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ h y - g y) x‖ ≤ Kh)
    (hvfb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ (vf y : V) - (vg y : V)) x‖ ≤ Kv) :
    ∀ k ≤ j, ∀ x ∈ S, ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
      (fun y ↦ incrementsModeFullReconstruction F hF c u h vf y -
        incrementsModeFullReconstruction F hF c v g vg y) x‖ ≤
      (2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
        max Mg ‖incrementsModeTransverseJet (m := m)‖) * Ku +
      ell * (Kv + (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) / 2) := by
  have hb := incrementsModeFullReconstruction_scaled_jets F hF c j O S hO hSO
    hG hJ hT0 (fun y ↦ u y - v y) (fun y ↦ h y - g y) (fun y ↦ vf y - vg y)
    (hu.sub hv) (hh.sub hg) (hvf.sub hvg) ell Mg Ku Kh Kv hell hell1
    hMg hKu hKh hGb hJb hT0b hub hhb hvfb
  intro k hk x hx
  have he : (fun y ↦ incrementsModeFullReconstruction F hF c u h vf y -
      incrementsModeFullReconstruction F hF c v g vg y) =ᶠ[𝓝 x]
      incrementsModeFullReconstruction F hF c (fun y ↦ u y - v y)
        (fun y ↦ h y - g y) (fun y ↦ vf y - vg y) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact incrementsModeFullReconstruction_sub F hF c O hO u v h g vf vg hu hv hy
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb k hk x hx

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsModeTransverseSourceCLM
#print axioms GlobalEmbedding.Paper.incrementsModeTransverseSource_eq_selector
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_tangent_normal
#print axioms GlobalEmbedding.Paper.incrementsModeTransverseSource_scaled_jets
#print axioms GlobalEmbedding.Paper.incrementsModeForcing_scaled_jets
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_contDiffOn
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_sub
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_real_smul
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_tsupport
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_scaled_jets
#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_difference_scaled_jets
