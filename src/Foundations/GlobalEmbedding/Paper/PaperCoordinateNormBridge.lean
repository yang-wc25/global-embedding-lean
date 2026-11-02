import GlobalEmbedding.Paper.CoordinateJetFiniteComparison
import GlobalEmbedding.Paper.CoordinatePartialIdentification
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.Sort

/-!
# Original coordinate partial norms on separate differentiation and supremum domains

Source: `main.tex`, notation225–238 and `lem:increments`.
O is the OPEN differentiation chart; S is the norm-evaluation domain, which may contain
compact parameter sets. All source and parameter coordinates are differentiated alike.
Sorted coordinate lists are the canonical fixed-order multiindex representatives.
-/

open scoped ContDiff ENNReal Topology

namespace GlobalEmbedding.Paper

/-- Literal scalar coordinate partials in a finite word, outermost coordinate first.
This is native within-line differentiation on the chart O, including for raw functions. -/
noncomputable def paperCoordinatePartial {n : ℕ} : List (Fin n) →
    ((Fin n → ℝ) → ℝ) → Set (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [], f, _, x => f x
  | i :: l, f, O, x => lineDerivWithin ℝ (paperCoordinatePartial l f O) O x (Pi.single i 1)

/-- Equality on the differentiation chart propagates through every actual partial.
Thus arbitrary ambient extensions of the same coordinate component are immaterial. -/
theorem paperCoordinatePartial_congr {n : ℕ} (l : List (Fin n))
    {f g : (Fin n → ℝ) → ℝ} {O : Set (Fin n → ℝ)} (h : Set.EqOn f g O) :
    Set.EqOn (paperCoordinatePartial l f O) (paperCoordinatePartial l g O) O := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro x hx
    exact lineDerivWithin_congr' ih hx

/-- A native coordinate within-line derivative remains smooth on its actual open chart. -/
theorem paper_coordinate_step_smooth {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x ↦ lineDerivWithin ℝ f O x (Pi.single i 1)) O := by
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen hO).1 hf |>.2
  have he : ContDiffOn ℝ ∞ (fun x ↦ fderiv ℝ f x (Pi.single i 1)) O :=
    hd.clm_apply contDiffOn_const
  apply he.congr
  intro x hx
  rw [lineDerivWithin_of_isOpen hO hx]
  exact (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp) |>.lineDeriv_eq_fderiv

/-- Every actual scalar partial tail remains locally smooth, without a global extension. -/
theorem paperCoordinatePartial_smooth {n : ℕ} (l : List (Fin n))
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) : ContDiffOn ℝ ∞ (paperCoordinatePartial l f O) O := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact paper_coordinate_step_smooth _ O hO ih i

/-- Adjacent actual coordinate partials commute by the native REAL C2 Schwarz theorem
on the actual smooth tail. No analytic higher-permutation theorem is invoked. -/
theorem paper_coordinate_steps_commute {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (i j : Fin n) (x : Fin n → ℝ) (hx : x ∈ O) :
    lineDerivWithin ℝ (fun y ↦ lineDerivWithin ℝ f O y (Pi.single j 1)) O x
        (Pi.single i 1) =
      lineDerivWithin ℝ (fun y ↦ lineDerivWithin ℝ f O y (Pi.single i 1)) O x
        (Pi.single j 1) := by
  have hstep (a : Fin n) :
      (fun y ↦ lineDerivWithin ℝ f O y (Pi.single a 1)) =ᶠ[nhds x]
        (fun y ↦ fderiv ℝ f y (Pi.single a 1)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [lineDerivWithin_of_isOpen hO hy]
    exact (hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)
      |>.lineDeriv_eq_fderiv
  rw [lineDerivWithin_of_isOpen hO hx, lineDerivWithin_of_isOpen hO hx,
    (hstep j).lineDeriv_eq, (hstep i).lineDeriv_eq]
  have hdwithin := ((contDiffOn_infty_iff_fderiv_of_isOpen hO).1 hf).2
  have hd := (hdwithin.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdiff (u : Fin n → ℝ) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y u) x :=
    hd.clm_apply (differentiableAt_const _)
  rw [(hdiff _).lineDeriv_eq_fderiv, (hdiff _).lineDeriv_eq_fderiv]
  have heval (u : Fin n → ℝ) :
      fderiv ℝ (fun y ↦ fderiv ℝ f y u) x = (fderiv ℝ (fderiv ℝ f) x).flip u := by
    have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
  rw [heval, heval]
  exact (hf.contDiffAt (hO.mem_nhds hx)).isSymmSndFDerivAt (by simp) _ _

/-- Finite coordinate word permutations preserve every actual partial on the original
smooth chart. The proof is only native finite-list induction, C2 Schwarz and locality. -/
theorem paperCoordinatePartial_perm {n : ℕ} {l r : List (Fin n)} (h : l.Perm r)
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) :
    Set.EqOn (paperCoordinatePartial l f O) (paperCoordinatePartial r f O) O := by
  induction h with
  | nil => intro x hx; rfl
  | cons i h ih =>
    intro x hx
    exact lineDerivWithin_congr' ih hx
  | swap i j l =>
    intro x hx
    exact paper_coordinate_steps_commute _ O hO (paperCoordinatePartial_smooth l f O hO hf)
      j i x hx
  | trans h₁ h₂ ih₁ ih₂ =>
    intro x hx
    exact (ih₁ hx).trans (ih₂ hx)

/-- The original extended componentwise coordinate Cj norm. Sorted words represent
fixed-order multiindices; the supremum domain S is separate from differentiation O. -/
noncomputable def paperCoordinateCj {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ l : {l : List (Fin n) // l.Pairwise (· ≤ ·) ∧ l.length ≤ j}, ⨆ x : S, ⨆ c : Fin q,
    ENNReal.ofReal ‖paperCoordinatePartial l.val (fun y ↦ f y c) O x‖

/-- On the original smooth chart, sorting changes no component partial. Consequently
fixed-order multiindices and all finite coordinate words give exactly the SAME norm. -/
theorem paperCoordinateCj_eq_all_words {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O) :
    paperCoordinateCj j f O S =
      ⨆ l : {l : List (Fin n) // l.length ≤ j}, ⨆ x : S, ⨆ c : Fin q,
        ENNReal.ofReal ‖paperCoordinatePartial l.val (fun y ↦ f y c) O x‖ := by
  apply le_antisymm
  · refine iSup_le fun l ↦ iSup_le fun x ↦ iSup_le fun c ↦ ?_
    exact le_iSup_of_le ⟨l.val, l.property.2⟩
      (le_iSup_of_le x (le_iSup_of_le c le_rfl))
  · refine iSup_le fun l ↦ iSup_le fun x ↦ iSup_le fun c ↦ ?_
    let r := l.val.mergeSort (· ≤ ·)
    have hp : r.Perm l.val := List.mergeSort_perm l.val (· ≤ ·)
    have hr : r.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) l.val
    have hlen : r.length ≤ j := hp.length_eq.trans_le l.property
    have heq := paperCoordinatePartial_perm hp (fun y ↦ f y c) O hO
      ((contDiffOn_pi.mp hf) c) (hSO x.property)
    rw [← heq]
    exact le_iSup_of_le ⟨r, hr, hlen⟩
      (le_iSup_of_le x (le_iSup_of_le c le_rfl))

/-- The actual original norm bounds every ordered partial, not only its sorted
representative. This keeps literal scalar derivatives available to quantitative callers. -/
theorem paper_coordinate_partial_le {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O) (l : List (Fin n)) (hl : l.length ≤ j)
    (x : S) (c : Fin q) :
    ENNReal.ofReal ‖paperCoordinatePartial l (fun y ↦ f y c) O x‖ ≤
      paperCoordinateCj j f O S := by
  rw [paperCoordinateCj_eq_all_words j f O S hO hSO hf]
  exact le_iSup_of_le ⟨l, hl⟩ (le_iSup_of_le x (le_iSup_of_le c le_rfl))

/-- The paper's finite buffered atlas MAX of actual component-partial norms. -/
noncomputable def paperAtlasCj {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ i, paperCoordinateCj j (f i) (O i) (S i)

/-- Literal cumulative weighted sum. base0 is the field norm; base2 is the map-twojet
norm. A full product coordinate index includes every stated parameter derivative. -/
noncomputable def paperAtlasWeighted {ι : Type*} [Fintype ι] {n q : ℕ} (base j : ℕ)
    (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (j + 1), ENNReal.ofReal ell ^ a * paperAtlasCj (a + base) f O S

/-- The list and finite-tuple encodings describe the SAME literal raw partial.
Only native list recursion is needed; the compiled derivative identification is reused. -/
theorem paperCoordinatePartial_ofFn {n k : ℕ} (σ : Fin k → Fin n)
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) :
    paperCoordinatePartial (List.ofFn σ) f O = coordinateWordPartialWithin k σ f O := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ]
    funext x
    simp only [paperCoordinatePartial, coordinateWordPartialWithin, ih]
    rfl

/-- The original fixed-order mixed-partial norm is EXACTLY the actual coefficient
gauge under original LOCAL smoothness, including the separate compact supremum set. -/
theorem paperCoordinateCj_eq_coordinateJetGauge {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O) :
    paperCoordinateCj j f O S = coordinateJetGauge j f S := by
  rw [paperCoordinateCj_eq_all_words j f O S hO hSO hf]
  apply le_antisymm
  · refine iSup_le fun l ↦ iSup_le fun x ↦ iSup_le fun c ↦ ?_
    have hl : List.ofFn (fun i : Fin l.val.length ↦ l.val.get i) = l.val :=
      List.ofFn_get l.val
    rw [← hl, paperCoordinatePartial_ofFn,
      coordinateWordPartialWithin_component f O hO hf l.val.length _ c x (hSO x.property)]
    exact coordinate_jet_coefficient_le_gauge f S l.property x _ c
  · refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
    have hk : (List.ofFn σ).length ≤ j := by simp; omega
    have hp := paper_coordinate_partial_le j f O S hO hSO hf (List.ofFn σ) hk x c
    rw [paperCoordinatePartial_ofFn,
      coordinateWordPartialWithin_component f O hO hf k.val σ c x (hSO x.property)] at hp
    rw [paperCoordinateCj_eq_all_words j f O S hO hSO hf] at hp
    exact hp

/-- Finiteness of the ORIGINAL partial norm is equivalent to genuine boundedness
of the actual Fréchet derivative ranges, not the default value of a real supremum. -/
theorem paperCoordinateCj_ne_top_iff {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O) :
    paperCoordinateCj j f O S ≠ ⊤ ↔
      ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖) := by
  rw [paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf]
  exact coordinateJetGauge_ne_top_iff j f S

/-- The original coordinate norm and existing Fréchet SUM norm have the actual
two-sided dimension/order comparison, with a guarded finite real projection. -/
theorem paperCoordinateCj_toReal_comparison {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (hfinite : paperCoordinateCj j f O S ≠ ⊤) :
    (paperCoordinateCj j f O S).toReal ≤ finiteCjNorm j f S ∧
      finiteCjNorm j f S ≤ (∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k) *
        (paperCoordinateCj j f O S).toReal := by
  rw [paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf] at hfinite ⊢
  exact coordinateJetGauge_toReal_comparison j f S hfinite

/-- Finite-chart MAX agrees with the coefficient MAX on the SAME actual chart functions. -/
theorem paperAtlasCj_eq_coordinateAtlasJetGauge {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasCj j f O S = coordinateAtlasJetGauge j f S := by
  apply iSup_congr
  intro i
  exact paperCoordinateCj_eq_coordinateJetGauge j (f i) (O i) (S i) (hO i) (hSO i) (hf i)

/-- Honest atlas finiteness uses actual jet boundedness in EVERY chart, with no
compact-closure assumption smuggled into a raw finite buffered atlas. -/
theorem paperAtlasCj_ne_top_iff {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasCj j f O S ≠ ⊤ ↔
      ∀ i, ∀ k ≤ j, BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖) := by
  rw [paperAtlasCj_eq_coordinateAtlasJetGauge j f O S hO hSO hf]
  exact coordinateAtlasJetGauge_ne_top_iff j f S

/-- Literal weighted sums agree termwise, including the original map-twojet C2 shift. -/
theorem paperAtlasWeighted_eq_coordinateAtlasWeightedGauge {ι : Type*} [Fintype ι]
    {n q : ℕ} (base j : ℕ) (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasWeighted base j ell f O S = coordinateAtlasWeightedGauge base j ell f S := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [paperAtlasCj_eq_coordinateAtlasJetGauge (a + base) f O S hO hSO hf]

/-- Actual finite weighted norms follow from ORIGINAL finite jet bounds on each
norm domain; all product-parameter coordinates are retained in the derivatives. -/
theorem paperAtlasWeighted_ne_top {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hbound : ∀ i, ∀ k ≤ j + base,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖)) :
    paperAtlasWeighted base j ell f O S ≠ ⊤ := by
  rw [paperAtlasWeighted_eq_coordinateAtlasWeightedGauge base j ell f O S hO hSO hf]
  exact coordinateAtlasWeightedGauge_ne_top base j ell f S hbound

/-- Every chart's existing real Fréchet SUM norm is bounded by the SAME finite atlas
MAX with only the fixed dimension/order factor. There is no chart-count factor. -/
theorem paperAtlasCj_finiteCjNorm_bound {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (hfinite : paperAtlasCj j f O S ≠ ⊤) (i : ι) :
    finiteCjNorm j (f i) (S i) ≤ (∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k) *
      (paperAtlasCj j f O S).toReal := by
  have hle : paperCoordinateCj j (f i) (O i) (S i) ≤ paperAtlasCj j f O S :=
    le_iSup (fun i ↦ paperCoordinateCj j (f i) (O i) (S i)) i
  have hfi := ne_top_of_le_ne_top hfinite hle
  have h := (paperCoordinateCj_toReal_comparison j (f i) (O i) (S i)
    (hO i) (hSO i) (hf i) hfi).2
  exact h.trans (mul_le_mul_of_nonneg_left
    ((ENNReal.toReal_le_toReal hfi hfinite).2 hle) (by positivity))

/-- Conversely one uniform bound on the existing actual finiteCj norms bounds the
original atlas MAX, provided their actual derivative ranges are genuinely bounded. -/
theorem paperAtlasCj_le_of_finiteCjNorm_bound {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hbdd : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖))
    (B : ℝ) (hB : ∀ i, finiteCjNorm j (f i) (S i) ≤ B) :
    paperAtlasCj j f O S ≤ ENNReal.ofReal B := by
  refine iSup_le fun i ↦ ?_
  rw [paperCoordinateCj_eq_coordinateJetGauge j (f i) (O i) (S i) (hO i) (hSO i) (hf i)]
  exact (coordinateJetGauge_le_finiteCjNorm j (f i) (S i) (hbdd i)).trans
    (ENNReal.ofReal_le_ofReal (hB i))

/-- With the ORIGINAL positive scale, finiteness of the literal weighted norm is
exactly true boundedness through j+base, including ALL compact-parameter derivatives. -/
theorem paperAtlasWeighted_ne_top_iff {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (hell : 0 < ell) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasWeighted base j ell f O S ≠ ⊤ ↔
      ∀ i, ∀ k ≤ j + base,
        BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖) := by
  constructor
  · intro hfinite
    have hsum : (∑ a ∈ Finset.range (j + 1), ENNReal.ofReal ell ^ a *
        paperAtlasCj (a + base) f O S) ≠ ⊤ := hfinite
    have hterm := ENNReal.sum_ne_top.1 hsum j (by simp)
    have hweight : ENNReal.ofReal ell ^ j ≠ 0 :=
      ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.2 hell) j
    have htop : paperAtlasCj (j + base) f O S ≠ ⊤ := by
      intro h
      rw [h, ENNReal.mul_top hweight] at hterm
      exact hterm rfl
    exact (paperAtlasCj_ne_top_iff (j + base) f O S hO hSO hf).1 htop
  · exact paperAtlasWeighted_ne_top base j ell f O S hO hSO hf

/-- The real weighted norm is its literal weighted sum ONLY after its actual
extended value is finite. The infinity-to-zero totalization is never used as a bound. -/
theorem paperAtlasWeighted_toReal {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hfinite : paperAtlasWeighted base j ell f O S ≠ ⊤) :
    (paperAtlasWeighted base j ell f O S).toReal =
      ∑ a ∈ Finset.range (j + 1), ell ^ a * (paperAtlasCj (a + base) f O S).toReal := by
  have hsum : (∑ a ∈ Finset.range (j + 1), ENNReal.ofReal ell ^ a *
      paperAtlasCj (a + base) f O S) ≠ ⊤ := hfinite
  change (∑ a ∈ Finset.range (j + 1), ENNReal.ofReal ell ^ a *
    paperAtlasCj (a + base) f O S).toReal = _
  rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.1 hsum)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hell]

/-- Every actual chart's weighted Fréchet SUM jets are controlled by the original
weighted atlas MAX with a dimension/order factor independent of the number of charts. -/
theorem paperAtlasWeighted_finiteCjNorm_bound {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (hell : 0 < ell) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : paperAtlasWeighted base j ell f O S ≠ ⊤) (i : ι) :
    (∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm (a + base) (f i) (S i)) ≤
      (∑ k ∈ Finset.range (j + base + 1), (n : ℝ) ^ k) *
        (paperAtlasWeighted base j ell f O S).toReal := by
  have hbdd := (paperAtlasWeighted_ne_top_iff base j ell hell f O S hO hSO hf).1 hfinite
  rw [paperAtlasWeighted_toReal base j ell hell.le f O S hfinite, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have haj : a ≤ j := by simpa using ha
  have hfi : paperAtlasCj (a + base) f O S ≠ ⊤ := by
    apply (paperAtlasCj_ne_top_iff (a + base) f O S hO hSO hf).2
    intro i k hk
    exact hbdd i k (by omega)
  have hn := paperAtlasCj_finiteCjNorm_bound (a + base) f O S hO hSO hf hfi i
  have hC : (∑ k ∈ Finset.range (a + base + 1), (n : ℝ) ^ k) ≤
      ∑ k ∈ Finset.range (j + base + 1), (n : ℝ) ^ k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro k hk hka
      positivity
  calc
    _ ≤ ell ^ a * ((∑ k ∈ Finset.range (a + base + 1), (n : ℝ) ^ k) *
        (paperAtlasCj (a + base) f O S).toReal) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hell.le a)
    _ ≤ ell ^ a * ((∑ k ∈ Finset.range (j + base + 1), (n : ℝ) ^ k) *
        (paperAtlasCj (a + base) f O S).toReal) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC ENNReal.toReal_nonneg)
        (pow_nonneg hell.le a)
    _ = _ := by ring

/-- Uniform actual Fréchet bounds at each order bound the original weighted atlas
norm by the SAME weighted bound profile, with no summation over chart labels. -/
theorem paperAtlasWeighted_le_of_finiteCjNorm_bound {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (hell : 0 < ell) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hbdd : ∀ i, ∀ k ≤ j + base,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖))
    (B : ℕ → ℝ) (hB0 : ∀ a ≤ j, 0 ≤ B a)
    (hB : ∀ a ≤ j, ∀ i, finiteCjNorm (a + base) (f i) (S i) ≤ B a) :
    (paperAtlasWeighted base j ell f O S).toReal ≤
      ∑ a ∈ Finset.range (j + 1), ell ^ a * B a := by
  have hfinite := paperAtlasWeighted_ne_top base j ell f O S hO hSO hf hbdd
  rw [paperAtlasWeighted_toReal base j ell hell.le f O S hfinite]
  apply Finset.sum_le_sum
  intro a ha
  have haj : a ≤ j := by simpa using ha
  have hbound : ∀ i, ∀ k ≤ a + base,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖) := by
    intro i k hk
    exact hbdd i k (by omega)
  have hfi := (paperAtlasCj_ne_top_iff (a + base) f O S hO hSO hf).2 hbound
  have hle := paperAtlasCj_le_of_finiteCjNorm_bound (a + base) f O S hO hSO hf hbound
    (B a) (hB a haj)
  have ht := (ENNReal.toReal_le_toReal hfi ENNReal.ofReal_ne_top).2 hle
  rw [ENNReal.toReal_ofReal (hB0 a haj)] at ht
  exact mul_le_mul_of_nonneg_left ht (pow_nonneg hell.le a)

/-- Actual fixed coordinate changes compare derivative norms by their true CLE norms.
Native exact pre/postcomposition applies even to totalized jets; no isometry or smooth
ambient extension is assumed. This supplies the PiSUP/EuclideanL2 comparison constants. -/
theorem paper_coordinate_change_jet_bound
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : X ≃L[ℝ] E) (b : F ≃L[ℝ] G) (f : E → F) (x : X) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (b ∘ f ∘ a) x‖ ≤
      ‖b.toContinuousLinearMap‖ * ‖iteratedFDeriv ℝ k f (a x)‖ *
        ‖a.toContinuousLinearMap‖ ^ k := by
  have ha : iteratedFDeriv ℝ k (f ∘ a) x =
      (iteratedFDeriv ℝ k f (a x)).compContinuousLinearMap
        (fun _ : Fin k ↦ a.toContinuousLinearMap) := by
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
      a.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ _) k
  rw [b.iteratedFDeriv_comp_left, ha]
  have hpre := (iteratedFDeriv ℝ k f (a x)).norm_compContinuousLinearMap_le
    (fun _ : Fin k ↦ a.toContinuousLinearMap)
  have hpost := b.toContinuousLinearMap.norm_compContinuousMultilinearMap_le
    ((iteratedFDeriv ℝ k f (a x)).compContinuousLinearMap (fun _ : Fin k ↦ a.toContinuousLinearMap))
  exact hpost.trans (by simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_assoc] using mul_le_mul_of_nonneg_left hpre (norm_nonneg b.toContinuousLinearMap))

/-- The SAME actual Euclidean map in PiSUP coordinate values, using native CLEs. -/
noncomputable def paperPiCoordinates {n q : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q)) :
    (Fin n → ℝ) → Fin q → ℝ :=
  (EuclideanSpace.equiv (Fin q) ℝ) ∘ F ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm

/-- Actual Pi coordinate jets have dimension/order constants, not false norm isometries. -/
theorem paperPiCoordinates_jet_bound {n q : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (y : Fin n → ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (paperPiCoordinates F) y‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).toContinuousLinearMap‖ *
        ‖iteratedFDeriv ℝ k F ((EuclideanSpace.equiv (Fin n) ℝ).symm y)‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ k :=
  paper_coordinate_change_jet_bound _ _ F y k

/-- The SAME original Euclidean jets are bounded conversely by their actual Pi jets.
The native inverse CLEs retain zero dimensions and introduce no chart-count constant. -/
theorem paperPiCoordinates_reverse_jet_bound {n q : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k F x‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ *
        ‖iteratedFDeriv ℝ k (paperPiCoordinates F) ((EuclideanSpace.equiv (Fin n) ℝ) x)‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ ^ k := by
  have hF : (EuclideanSpace.equiv (Fin q) ℝ).symm ∘ paperPiCoordinates F ∘
      (EuclideanSpace.equiv (Fin n) ℝ) = F := by
    funext y
    simp [paperPiCoordinates]
  have h := paper_coordinate_change_jet_bound (EuclideanSpace.equiv (Fin n) ℝ)
    (EuclideanSpace.equiv (Fin q) ℝ).symm (paperPiCoordinates F) x k
  rwa [hF] at h

end GlobalEmbedding.Paper
