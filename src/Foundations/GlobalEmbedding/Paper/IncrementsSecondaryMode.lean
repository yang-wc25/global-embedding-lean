import GlobalEmbedding.Paper.IncrementsModeCoefficientRegularity
import GlobalEmbedding.Paper.IncrementsModeFullReconstruction
import GlobalEmbedding.Paper.IncrementsActualModeSize
import GlobalEmbedding.Paper.IncrementsModeRowResidual
import GlobalEmbedding.Paper.IncrementsModeActualFiniteResidual

/-!
# Actual forcing source for the original secondary mode

Source: `main.tex`, lem:increments664–668. The free normal is zero and the
original forcing is retained. Only fixed native source CLMs are constructed;
actual J, R, full Z, finite U and the physical metric rows are reused.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The fixed original source rows, before the actual J h_H correction.
Its true Pi-to-Euclidean operator norm is retained. -/
def incrementsModeForcingSourceProjection : Source →L[ℝ] D :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ Fin.cases
      ((1 / 2 : ℝ) • ((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
        (Fin (m + 1) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (0 : Fin (m + 1)) :
          Source →L[ℝ] (Fin (m + 1) → ℝ))))
      (fun a ↦ (ContinuousLinearMap.proj a.succ :
        (Fin (m + 1) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (0 : Fin (m + 1)) :
          Source →L[ℝ] (Fin (m + 1) → ℝ))) i)

/-- Exact original 11 half and unweighted mixed rows of the fixed source map. -/
theorem incrementsModeForcingSourceProjection_apply (h : Source) (i : Fin (m + 1)) :
    incrementsModeForcingSourceProjection h i =
      Fin.cases (h 0 0 / 2) (fun a ↦ h 0 a.succ) i := by
  refine Fin.cases ?_ (fun a ↦ ?_) i
  · simp [incrementsModeForcingSourceProjection]
    ring
  · simp [incrementsModeForcingSourceProjection]

/-- The fixed bilinear true-B row packing, represented by native continuous
linear maps. Its actual norm, including the Euclidean conversion, is retained. -/
def incrementsModeForcingSourcePairing :
    (Fin (m + 1) → V) →L[ℝ] (V →L[ℝ] D) :=
  ∑ i : Fin (m + 1),
    ((ContinuousLinearMap.compL ℝ V ℝ D)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        ((incrementsModeRowWeight i / 2) • EuclideanSpace.single i 1))).comp
      ((innerSL ℝ).comp (ContinuousLinearMap.proj i))

/-- Component evaluation of the fixed source packing keeps the original half
in row11 and minus-one coefficient of J h_H in every mixed source. -/
theorem incrementsModeForcingSourcePairing_apply
    (b : Fin (m + 1) → V) (v : V) (i : Fin (m + 1)) :
    incrementsModeForcingSourcePairing b v i =
      (incrementsModeRowWeight i / 2) * inner ℝ (b i) v := by
  simp [incrementsModeForcingSourcePairing, ContinuousLinearMap.compL_apply,
    Pi.single_apply, ite_mul, mul_comm]

section OriginalMode
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- Exact actual secondary source, with zero free normal. No desired source
identity is an input; the canonical original source and J are evaluated. -/
theorem incrementsModeSource_zeroFree_eq (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (h : D → Source) (x : D) :
    incrementsModeSource F hF c h (fun _ ↦ 0) x =
      incrementsModeForcingSourceProjection (h x) -
        incrementsModeForcingSourcePairing
          (fun i ↦ (incrementsModeSecondForm F hF c x 0 i : V))
          (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x) : V) := by
  ext i
  change incrementsModeSource F hF c h (fun _ ↦ 0) x i =
    incrementsModeForcingSourceProjection (h x) i -
      incrementsModeForcingSourcePairing
        (fun a ↦ (incrementsModeSecondForm F hF c x 0 a : V))
        (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x) : V) i
  rw [incrementsModeForcingSourceProjection_apply, incrementsModeForcingSourcePairing_apply]
  simp [incrementsModeSource, Submodule.coe_inner]

/-- The genuine vf=0 source is smooth from the actual B/J fields and the
original forcing. This is not the existing h=0 primary-source theorem. -/
theorem incrementsModeSource_zeroFree_contDiffOn (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (h : D → Source)
    (O : Set D)
    (hB : ContDiffOn ℝ ∞
      (fun x i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x ↦ (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hh : ContDiffOn ℝ ∞ h O) :
    ContDiffOn ℝ ∞ (fun x ↦ incrementsModeSource F hF c h (fun _ ↦ 0) x) O := by
  have hs := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  have hj := hJ.clm_apply hs
  have hb := incrementsModeForcingSourcePairing.contDiff.comp_contDiffOn hB
  have hp := incrementsModeForcingSourceProjection.contDiff.comp_contDiffOn hh
  apply (hp.sub (hb.clm_apply hj)).congr
  intro x hx
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ← incrementsModeTransverseSource_eq_selector] using
    incrementsModeSource_zeroFree_eq F hF c h x

/-- Actual forcing-to-source jets consume NO additional derivatives of h.
All input bounds are on the original h and actual B/J fields; a k bound is
proved here rather than supplied. Native operator norms are kept exactly. -/
theorem incrementsModeSource_zeroFree_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (n : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (h : D → Source)
    (hB : ContDiffOn ℝ ∞
      (fun x i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x ↦ (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hh : ContDiffOn ℝ ∞ h O)
    (ell MB MJ Kh : ℝ) (hell : 0 ≤ ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hKh : 0 ≤ Kh)
    (hBb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V)) x‖ ≤ MB)
    (hJb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ MJ)
    (hhb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h x‖ ≤ Kh) :
    ∀ k ≤ n, ∀ x ∈ S, ell ^ k *
      ‖iteratedFDeriv ℝ k (fun y ↦ incrementsModeSource F hF c h (fun _ ↦ 0) y) x‖ ≤
      (‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
        ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
          ‖incrementsModeTransverseSourceCLM (m := m)‖) * Kh := by
  let P := incrementsModeForcingSourceProjection ∘ h
  let Qb := incrementsModeForcingSourcePairing ∘
    (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V))
  let JH := fun y ↦
    (incrementsModeCoordinateJ F hF c y (incrementsModeTransverseSource h y) : V)
  have hP : ContDiffOn ℝ ∞ P O :=
    incrementsModeForcingSourceProjection.contDiff.comp_contDiffOn hh
  have hQb : ContDiffOn ℝ ∞ Qb O :=
    incrementsModeForcingSourcePairing.contDiff.comp_contDiffOn hB
  have hJH : ContDiffOn ℝ ∞ JH O := by
    simpa only [JH, Function.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ← incrementsModeTransverseSource_eq_selector] using
      hJ.clm_apply (incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh)
  have hJHb := incrementsModeForcing_scaled_jets F hF c n O S hO hSO hJ h hh
    ell MJ Kh hell hMJ hKh hJb hhb
  have heq : (fun y ↦ incrementsModeSource F hF c h (fun _ ↦ 0) y) =
      fun y ↦ P y - Qb y (JH y) := by
    funext y
    exact incrementsModeSource_zeroFree_eq F hF c h y
  rw [heq]
  intro k hk x hx
  have hPb : ell ^ k * ‖iteratedFDeriv ℝ k P x‖ ≤
      ‖incrementsModeForcingSourceProjection (m := m)‖ * Kh := by
    calc
      _ ≤ ell ^ k * (‖incrementsModeForcingSourceProjection (m := m)‖ *
          ‖iteratedFDeriv ℝ k h x‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _
          (hh.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ = ‖incrementsModeForcingSourceProjection (m := m)‖ *
          (ell ^ k * ‖iteratedFDeriv ℝ k h x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hhb k hk x hx) (norm_nonneg _)
  have hQbb (i : ℕ) (hi : i ≤ k) : ell ^ i * ‖iteratedFDeriv ℝ i Qb x‖ ≤
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB := by
    calc
      _ ≤ ell ^ i * (‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ *
          ‖iteratedFDeriv ℝ i
            (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V)) x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _
          (hB.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ = ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ *
          (ell ^ i * ‖iteratedFDeriv ℝ i
            (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V)) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBb i (hi.trans hk) x hx)
        (norm_nonneg (incrementsModeForcingSourcePairing (m := m) (N := N)))
  have hprod := scaled_clm_apply O hO Qb JH hQb hJH k 0 ell
    (‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB)
    (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) hell hQbb
    (fun i hi ↦ by simpa only [Nat.add_zero] using hJHb i (hi.trans hk) x hx) (hSO hx)
  have hp := (hP.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hq := ((hQb.clm_apply hJH).contDiffAt (hO.mem_nhds (hSO hx))).of_le
    (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [fun_iteratedFDeriv_sub_apply hp hq]
  calc
    _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k P x‖ +
        ‖iteratedFDeriv ℝ k (fun y ↦ Qb y (JH y)) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = ell ^ k * ‖iteratedFDeriv ℝ k P x‖ +
        ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ Qb y (JH y)) x‖ := by ring
    _ ≤ ‖incrementsModeForcingSourceProjection (m := m)‖ * Kh +
        2 ^ k * (‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB) *
          (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) :=
      add_le_add hPb (by simpa only [Nat.add_zero] using hprod)
    _ ≤ ‖incrementsModeForcingSourceProjection (m := m)‖ * Kh +
        2 ^ n * (‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB) *
          (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      gcongr
      norm_num
    _ = _ := by rw [pow_add]; ring

/-- Native complex channels of the actual nonzero forcing source are smooth;
no complex normal bundle or desired source-regularity input is introduced. -/
theorem incrementsModeComplexSource_zeroFree_contDiffOn (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (hR hI : D → Source)
    (O : Set D)
    (hB : ContDiffOn ℝ ∞
      (fun x i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x ↦ (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O) :
    ContDiffOn ℝ ∞ (fun x ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) x) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) x)) O := by
  have hr := incrementsModeSource_zeroFree_contDiffOn F hF c hR O hB hJ hhR
  have hi := incrementsModeSource_zeroFree_contDiffOn F hF c hI O hB hJ hhI
  exact (incrementsModeComplexInclude.contDiff.comp_contDiffOn hr).add
    ((incrementsModeComplexInclude.contDiff.comp_contDiffOn hi).const_smul Complex.I)

/-- The actual complex k(h,0) is bounded from the two ORIGINAL forcing channels.
The true inclusion norm is retained, and h loses no derivatives in this step. -/
theorem incrementsModeComplexSource_zeroFree_scaled_jets (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (n : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hR hI : D → Source)
    (hB : ContDiffOn ℝ ∞
      (fun x i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x ↦ (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (ell MB MJ KhR KhI : ℝ) (hell : 0 ≤ ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hKhR : 0 ≤ KhR) (hKhI : 0 ≤ KhI)
    (hBb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V)) x‖ ≤ MB)
    (hJb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ MJ)
    (hhRb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR x‖ ≤ KhR)
    (hhIb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI x‖ ≤ KhI) :
    let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
        ‖incrementsModeTransverseSourceCLM (m := m)‖
    ∀ k ≤ n, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦
      incrementsModeComplexInclude (incrementsModeSource F hF c hR (fun _ ↦ 0) y) +
        Complex.I • incrementsModeComplexInclude
          (incrementsModeSource F hF c hI (fun _ ↦ 0) y)) x‖ ≤
      ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI) := by
  dsimp only
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  let kr := fun y ↦ incrementsModeSource F hF c hR (fun _ ↦ 0) y
  let ki := fun y ↦ incrementsModeSource F hF c hI (fun _ ↦ 0) y
  have hr := incrementsModeSource_zeroFree_contDiffOn F hF c hR O hB hJ hhR
  have hi := incrementsModeSource_zeroFree_contDiffOn F hF c hI O hB hJ hhI
  have hrb := incrementsModeSource_zeroFree_scaled_jets F hF c n O S hO hSO hR
    hB hJ hhR ell MB MJ KhR hell hMB hMJ hKhR hBb hJb hhRb
  have hib := incrementsModeSource_zeroFree_scaled_jets F hF c n O S hO hSO hI
    hB hJ hhI ell MB MJ KhI hell hMB hMJ hKhI hBb hJb hhIb
  have hcr := incrementsModeComplexInclude.contDiff.comp_contDiffOn hr
  have hci := incrementsModeComplexInclude.contDiff.comp_contDiffOn hi
  intro k hk x hx
  have hinc (f : D → D) (hf : ContDiffOn ℝ ∞ f O) (K : ℝ)
      (hb : ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ K) :
      ell ^ k * ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ f) x‖ ≤
        ‖incrementsModeComplexInclude (m := m)‖ * K := by
    calc
      _ ≤ ell ^ k * (‖incrementsModeComplexInclude (m := m)‖ *
          ‖iteratedFDeriv ℝ k f x‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _
          (hf.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ = ‖incrementsModeComplexInclude (m := m)‖ *
          (ell ^ k * ‖iteratedFDeriv ℝ k f x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hdr := (hcr.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hdi := (hci.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [Function.comp_def] at hdr hdi
  rw [fun_iteratedFDeriv_add_apply hdr (hdi.const_smul Complex.I),
    iteratedFDeriv_const_smul_apply' hdi]
  calc
    _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) x‖ +
        ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Function.comp_def, kr, ki, norm_smul, Complex.norm_I, one_mul] using norm_add_le
        (iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) x)
        (Complex.I • iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) x)
    _ = ell ^ k * ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) x‖ +
        ell ^ k * ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) x‖ := by ring
    _ ≤ ‖incrementsModeComplexInclude (m := m)‖ * (Ck * KhR) +
        ‖incrementsModeComplexInclude (m := m)‖ * (Ck * KhI) :=
      add_le_add (hinc kr hr _ (hrb k hk x hx)) (hinc ki hi _ (hib k hk x hx))
    _ = _ := by dsimp only [Ck]; ring

/-- SAME actual secondary finite U and full inhomogeneous Z have genuine size
bounds derived from h and actual geometry. The leading tau pays the one slow
reconstruction derivative. Only tau/ell<=1 is used, with p fixed before j. -/
theorem increments_secondary_mode_bounds (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (n p j : ℕ) (hbudget : j + 1 + p ≤ n)
    (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hR hI : D → Source)
    (hBR : ContDiffOn ℝ ∞
      (fun x i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x ↦ (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hG : ContDiffOn ℝ ∞ (fun x ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) x)) O)
    (hT : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (ell τ Mgeom KhR KhI : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hτ : 0 < τ) (hτell : τ ≤ ell)
    (hM : 0 ≤ Mgeom) (hKhR : 0 ≤ KhR) (hKhI : 0 ≤ KhI)
    (hBRb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y a ↦ (incrementsModeSecondForm F hF c y 0 a : V)) x‖ ≤ Mgeom)
    (hJb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c y)) x‖ ≤ Mgeom)
    (hGb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) x‖ ≤ Mgeom)
    (hTb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F c) x‖ ≤ Mgeom)
    (hAb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mgeom)
    (hBb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mgeom)
    (hhRb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR x‖ ≤ KhR)
    (hhIb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI x‖ ≤ KhI) :
    let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mgeom * Mgeom *
        ‖incrementsModeTransverseSourceCLM (m := m)‖
    let Kc := ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI)
    let Profile := ∑ a ∈ Finset.range p, (2 * 2 ^ n * Mgeom) ^ a
    let CR := 2 ^ j * Mgeom + 2 * 2 ^ (j + j) * Mgeom *
      max Mgeom ‖incrementsModeTransverseJet (m := m)‖
    let CH := (2 ^ j * Mgeom * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
    let k := fun x ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) x) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) x)
    let U := incrementsActualModeSum (incrementsModeComplexFirstOrderA F hF c)
      (incrementsModeComplexFirstOrderB F hF c) ((τ : ℂ) / Complex.I) p k
    (∀ r ≤ j + 1, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r U x‖ ≤ τ * Kc * Profile) ∧
    (∀ r, r + p ≤ n → ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
      (fun z ↦ ((τ : ℂ) / Complex.I)⁻¹ • U z +
        incrementsModeComplexReducedOperator F hF c U z - k z) x‖ ≤
      (2 * 2 ^ n * Mgeom) ^ p * (τ / ell) ^ p * Kc) ∧
    (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
      (incrementsModeFullReconstruction F hF c (incrementsModeRealPart ∘ U)
        hR (fun _ ↦ 0)) x‖ ≤
      CR * ‖incrementsModeRealPart (m := m)‖ * Kc * Profile + CH * KhR) ∧
    (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
      (incrementsModeFullReconstruction F hF c (incrementsModeImagPart ∘ U)
        hI (fun _ ↦ 0)) x‖ ≤
      CR * ‖incrementsModeImagPart (m := m)‖ * Kc * Profile + CH * KhI) := by
  dsimp only
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mgeom * Mgeom *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  let Kc := ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI)
  let Cn := 2 * 2 ^ n * Mgeom
  let Profile := ∑ a ∈ Finset.range p, Cn ^ a
  let CR := 2 ^ j * Mgeom + 2 * 2 ^ (j + j) * Mgeom *
    max Mgeom ‖incrementsModeTransverseJet (m := m)‖
  let CH := (2 ^ j * Mgeom * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
  let k := fun x ↦ incrementsModeComplexInclude
    (incrementsModeSource F hF c hR (fun _ ↦ 0) x) + Complex.I •
    incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) x)
  let U := incrementsActualModeSum (incrementsModeComplexFirstOrderA F hF c)
    (incrementsModeComplexFirstOrderB F hF c) ((τ : ℂ) / Complex.I) p k
  have hKc : 0 ≤ Kc := by dsimp [Kc, Ck]; positivity
  have hCn : 0 ≤ Cn := by dsimp [Cn]; positivity
  have hProfile : 0 ≤ Profile := Finset.sum_nonneg fun _ _ ↦ pow_nonneg hCn _
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  have hk := incrementsModeComplexSource_zeroFree_contDiffOn F hF c hR hI O hBR hJ hhR hhI
  have hkb := incrementsModeComplexSource_zeroFree_scaled_jets F hF c n O S hO hSO hR hI
    hBR hJ hhR hhI ell Mgeom Mgeom KhR KhI hell.le hM hM hKhR hKhI hBRb hJb hhRb hhIb
  have hu : ContDiffOn ℝ ∞ U O := increments_actual_mode_sum_contDiffOn _ _ _ _ _
    O hO hA hB hk
  have hratio : Cn * τ / ell ≤ Cn :=
    (div_le_iff₀ hell).2 (mul_le_mul_of_nonneg_left hτell hCn)
  have hsum : (∑ a ∈ Finset.range p, (Cn * τ / ell) ^ a) ≤ Profile :=
    Finset.sum_le_sum fun a _ ↦ pow_le_pow_left₀ (by positivity) hratio a
  have hUb : ∀ r ≤ j + 1, ∀ x ∈ S,
      ell ^ r * ‖iteratedFDeriv ℝ r U x‖ ≤ τ * Kc * Profile := by
    intro r hr x hx
    have hraw := incrementsModeActualSum_scaled_jet_tau F hF c n p O S hO hSO τ hτ k
      hA hB hk ell Mgeom Kc hell hell1 hM hKc hAb hBb hkb r (by omega) x hx
    exact hraw.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hτ.le hKc))
  have hZ (L : Cdata →L[ℝ] D) (H : D → Source) (hH : ContDiffOn ℝ ∞ H O)
      (KH : ℝ) (hKH : 0 ≤ KH)
      (hHb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i H x‖ ≤ KH) :
      ∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (incrementsModeFullReconstruction F hF c (L ∘ U) H (fun _ ↦ 0)) x‖ ≤
        CR * ‖L‖ * Kc * Profile + CH * KH := by
    let Ku := ‖L‖ * τ * Kc * Profile
    have hKu : 0 ≤ Ku := by dsimp [Ku]; positivity
    have hv := L.contDiff.comp_contDiffOn hu
    have hvb : ∀ i ≤ j + 1, ∀ x ∈ S,
        ell ^ i * ‖iteratedFDeriv ℝ i (L ∘ U) x‖ ≤ Ku := by
      intro i hi x hx
      calc
        _ ≤ ell ^ i * (‖L‖ * ‖iteratedFDeriv ℝ i U x‖) := mul_le_mul_of_nonneg_left
          (L.norm_iteratedFDeriv_comp_left (hu.contDiffAt (hO.mem_nhds (hSO hx)))
            (by simp)) (by positivity)
        _ = ‖L‖ * (ell ^ i * ‖iteratedFDeriv ℝ i U x‖) := by ring
        _ ≤ ‖L‖ * (τ * Kc * Profile) :=
          mul_le_mul_of_nonneg_left (hUb i hi x hx) (norm_nonneg L)
        _ = Ku := by dsimp [Ku]; ring
    have hz := incrementsModeFullReconstruction_scaled_jets F hF c j O S hO hSO
      hG hJ hT (L ∘ U) H (fun _ ↦ 0) hv hH (by simpa using contDiffOn_const (c := (0 : V)))
      ell Mgeom Ku KH 0 hell hell1 hM hKu hKH hGb
      (fun i hi x hx ↦ hJb i (by omega) x hx) hTb hvb hHb (by intros; simp)
    intro r hr x hx
    have he : ell ^ (r + 1) * ‖iteratedFDeriv ℝ r
        (incrementsModeFullReconstruction F hF c (L ∘ U) H (fun _ ↦ 0)) x‖ =
        ell * (ell ^ r * ‖iteratedFDeriv ℝ r
          (incrementsModeFullReconstruction F hF c (L ∘ U) H (fun _ ↦ 0)) x‖) := by
      rw [pow_succ]
      ring
    have hb := hz r hr x hx
    rw [he] at hb
    have hCH : 2 ^ j * Mgeom * ‖incrementsModeTransverseSourceCLM (m := m)‖ * KH / 2 =
        CH * KH := by dsimp [CH]; ring
    rw [hCH] at hb
    have hscale : CR * Ku + ell * (0 + CH * KH) ≤
        ell * (CR * ‖L‖ * Kc * Profile + CH * KH) := by
      calc
        _ = (CR * ‖L‖ * Kc * Profile) * τ + ell * (CH * KH) := by dsimp [Ku]; ring
        _ ≤ (CR * ‖L‖ * Kc * Profile) * ell + ell * (CH * KH) :=
          add_le_add (mul_le_mul_of_nonneg_left hτell
            (show 0 ≤ CR * ‖L‖ * Kc * Profile by positivity)) (le_refl _)
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hell).mp (hb.trans hscale)
  refine ⟨hUb, ?_, ?_, ?_⟩
  · intro r hr x hx
    exact incrementsModeActualFiniteResidual_scaled_jet_tau F hF c n p O S hO hSO τ hτ k
      hA hB hk ell Mgeom Kc hell hell1 hM hKc hAb hBb hkb r hr x hx
  · exact hZ incrementsModeRealPart hR hhR KhR hKhR
      (fun i hi x hx ↦ hhRb i (by omega) x hx)
  · exact hZ incrementsModeImagPart hI hhI KhI hKhI
      (fun i hi x hx ↦ hhIb i (by omega) x hx)

end OriginalMode
section ActualChart
local notation "𝓙" => 𝓘(ℝ, D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- The ORIGINAL actual secondary mode has physical residual -2 times the
finite iterate in row11, minus the iterate in mixed rows, and zero transverse.
All source/U/normal differentiability is derived from the original smooth data
and accepted geometry. No desired PDE, solver or metric identity is an input. -/
theorem increments_secondary_mode_physical_rows
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm z)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm z)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm z a.succ)
      (β.comp β.adjoint).IsInvertible)
    (hR hI : D → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O) :
    let c := (extChartAt 𝓙 y).symm
    let α := (τ : ℂ) / Complex.I
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) z)
    let U := incrementsActualModeSum A B α p k
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (U z)) hR (fun _ ↦ 0)
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (U z)) hI (fun _ ↦ 0)
    let WR := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).re)
    let WI := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).im)
    let err := fun i j ↦ Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation (F ∘ c) WR x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) WI x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
      ((hR x i j : ℂ) + Complex.I * (hI x i j : ℂ))
    let v := ((incrementsActualModeStep A B α)^[p] k) x
    err 0 0 = -2 * v 0 ∧ (∀ a : Fin m, err 0 a.succ = -v a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
  intro c α A B k U ZR ZI WR WI err v
  let uR := fun z ↦ incrementsModeRealPart (U z)
  let uI := fun z ↦ incrementsModeImagPart (U z)
  let e := α⁻¹ • U x + incrementsModeComplexReducedOperator F hF c U x - k x
  let νR := fun z ↦ (0 : normalSpace (I := 𝓙) F (c z)) +
    incrementsModeCoordinateJ F hF c z (incrementsModeTransverseTensor F c uR z) -
      (1 / 2 : ℝ) • incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
  let νI := fun z ↦ (0 : normalSpace (I := 𝓙) F (c z)) +
    incrementsModeCoordinateJ F hF c z (incrementsModeTransverseTensor F c uI z) -
      (1 / 2 : ℝ) • incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
  have hJ : ContDiffOn ℝ ∞ (fun z ↦ (normalSpace (I := 𝓙) F (c z)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c z)) O := by
    apply (incrementsModeAmbientJ_contDiffOn F hF y O hO hOt hinj hfree).congr
    intro z hz
    exact incrementsModeCoordinateJ_ambient F hF c z
  have hBR : ContDiffOn ℝ ∞
      (fun z i ↦ (incrementsModeSecondForm F hF c z 0 i : V)) O :=
    contDiffOn_pi.mpr fun i ↦ incrementsModeSecondForm_contDiffOn F hF y O hO hOt hinj 0 i
  have hA := incrementsModeComplexFirstOrderA_contDiffOn F hF y O hO hOt hinj hfree
  have hB := incrementsModeComplexFirstOrderB_contDiffOn F hF y O hO hOt hinj hfree
  have hk := incrementsModeComplexSource_zeroFree_contDiffOn F hF c hR hI O hBR hJ hhR hhI
  have hu : ContDiffOn ℝ ∞ U O :=
    increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk
  have hur : ContDiffOn ℝ ∞ uR O := incrementsModeRealPart.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ uI O := incrementsModeImagPart.contDiff.comp_contDiffOn hu
  have hT := incrementsModeTransverseValue_contDiffOn F hF y O hO hOt hinj
  have hνR : ContDiffOn ℝ ∞ (fun z ↦ (νR z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uR hur
    have hh := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hhR
    simpa only [νR, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← incrementsModeTransverseSource_eq_selector] using
      (hJ.clm_apply ht).sub ((hJ.clm_apply hh).const_smul (1 / 2 : ℝ))
  have hνI : ContDiffOn ℝ ∞ (fun z ↦ (νI z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uI hui
    have hh := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hhI
    simpa only [νI, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← incrementsModeTransverseSource_eq_selector] using
      (hJ.clm_apply ht).sub ((hJ.clm_apply hh).const_smul (1 / 2 : ℝ))
  have hd := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hr := increments_mode_physical_residual_rows F hF y O hO hOt hinj U hR hI
    (fun _ ↦ 0) (fun _ ↦ 0) τ x hx hd (hfree x hx) (map_zero _) (map_zero _)
  dsimp only at hr
  have hdνR := (hνR.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdνI := (hνI.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  specialize hr hdνR hdνI
  change err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
    ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 at hr
  have hα : α ≠ 0 := by
    dsimp [α]
    exact div_ne_zero (by exact_mod_cast hτ.ne') Complex.I_ne_zero
  have he := incrementsModeActualFiniteResidual_eq F hF c α hα p k O hO hA hB hk x hx
  change e = -v at he
  rcases hr with ⟨hr0, hr1, hrt⟩
  refine ⟨?_, ?_, hrt⟩
  · rw [he] at hr0
    simpa only [Pi.neg_apply, mul_neg, neg_mul] using hr0
  · intro a
    have ha := hr1 a
    rw [he] at ha
    simpa only [Pi.neg_apply] using ha

end ActualChart

end GlobalEmbedding.Paper
