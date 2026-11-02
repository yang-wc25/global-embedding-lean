import NormalPolar.PassiveOriginalRawNorm

/-! Literal coordinate-partial transport for an increasing coordinate
injection. Besides the original source block, this handles the parameter
block in the unchanged source-first original coordinate convention. The
proof uses the same one-variable line functions and retains the original
sorted partial words. No differentiability or desired norm estimate is an
input. -/

noncomputable section
open Set Function
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {a b q : ℕ}

theorem passiveOriginal_partial_zero (l : List (Fin b)) (D : Set (Fin b → ℝ))
    (y : Fin b → ℝ) : paperCoordinatePartial l (fun _ => (0 : ℝ)) D y = 0 := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih =>
    change lineDerivWithin ℝ (paperCoordinatePartial l (fun _ => (0 : ℝ)) D) D y _ = 0
    have he : paperCoordinatePartial l (fun _ => (0 : ℝ)) D = fun _ => 0 := funext ih
    rw [he]
    simp [lineDerivWithin]

theorem passiveOriginal_partial_component_le (j : ℕ)
    (f : (Fin b → ℝ) → Fin q → ℝ) (D T : Set (Fin b → ℝ))
    (l : List (Fin b)) (hl : l.Pairwise (· ≤ ·)) (hlen : l.length ≤ j)
    (y : Fin b → ℝ) (hy : y ∈ T) (c : Fin q) :
    ENNReal.ofReal ‖paperCoordinatePartial l (fun z => f z c) D y‖ ≤ paperCoordinateCj j f D T :=
  le_iSup_of_le ⟨l,hl,hlen⟩ (le_iSup_of_le ⟨y,hy⟩ (le_iSup_of_le c le_rfl))

def passiveOriginalInjectedProjection (e : Fin a ↪ Fin b) :
    (Fin b → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))

@[simp] theorem passiveOriginalInjectedProjection_apply (e : Fin a ↪ Fin b)
    (y : Fin b → ℝ) (i : Fin a) : passiveOriginalInjectedProjection e y i = y (e i) := rfl

theorem passiveOriginalInjectedProjection_single (e : Fin a ↪ Fin b) (i : Fin a) :
    passiveOriginalInjectedProjection e (Pi.single (e i) 1) = Pi.single i 1 := by
  ext j
  simp only [passiveOriginalInjectedProjection_apply,Pi.single_apply]
  simp

theorem passiveOriginalInjectedProjection_single_outside (e : Fin a ↪ Fin b)
    (i : Fin b) (hi : i ∉ range e) : passiveOriginalInjectedProjection e (Pi.single i 1) = 0 := by
  ext j
  have hne : i ≠ e j := fun h => hi ⟨j,h.symm⟩
  simp only [passiveOriginalInjectedProjection_apply,Pi.single_apply,Pi.zero_apply]
  simp [hne,Ne.symm hne]

theorem passiveOriginal_injected_lineDeriv
    (e : Fin a ↪ Fin b) (f : (Fin a → ℝ) → ℝ)
    (O : Set (Fin a → ℝ)) (hO : IsOpen O)
    (D : Set (Fin b → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalInjectedProjection e) D O)
    (x : Fin b → ℝ) (hx : x ∈ D) (i : Fin a) :
    lineDerivWithin ℝ (f ∘ passiveOriginalInjectedProjection e) D x (Pi.single (e i) 1) =
      lineDerivWithin ℝ f O (passiveOriginalInjectedProjection e x) (Pi.single i 1) := by
  rw [lineDerivWithin_of_isOpen hD hx,lineDerivWithin_of_isOpen hO (hDO hx)]
  unfold lineDeriv
  congr 1
  funext t
  simp only [Function.comp_apply,map_add,map_smul,passiveOriginalInjectedProjection_single]

theorem passiveOriginal_injected_partial
    (e : Fin a ↪ Fin b) (f : (Fin a → ℝ) → ℝ)
    (O : Set (Fin a → ℝ)) (hO : IsOpen O)
    (D : Set (Fin b → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalInjectedProjection e) D O) (l : List (Fin a)) :
    EqOn (paperCoordinatePartial (l.map e) (f ∘ passiveOriginalInjectedProjection e) D)
      ((paperCoordinatePartial l f O) ∘ passiveOriginalInjectedProjection e) D := by
  induction l with
  | nil => intro x _; rfl
  | cons i l ih =>
    intro x hx
    change lineDerivWithin ℝ _ D x _ = lineDerivWithin ℝ _ O _ _
    rw [lineDerivWithin_congr' ih hx]
    exact passiveOriginal_injected_lineDeriv e _ O hO D hD hDO x hx i

theorem passiveOriginal_injected_word
    (e : Fin a ↪ Fin b) (f : (Fin a → ℝ) → ℝ)
    (O : Set (Fin a → ℝ)) (hO : IsOpen O)
    (D : Set (Fin b → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalInjectedProjection e) D O) (l : List (Fin b)) :
    (∃ l₀ : List (Fin a), l₀.map e = l) ∨
      EqOn (paperCoordinatePartial l (f ∘ passiveOriginalInjectedProjection e) D) (fun _ => 0) D := by
  induction l with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons i l ih =>
    rcases ih with ⟨l₀,hl₀⟩ | hz
    · by_cases hi : i ∈ range e
      · obtain ⟨i₀,hi₀⟩ := hi
        exact Or.inl ⟨i₀::l₀,by simp only [List.map_cons,hi₀,hl₀]⟩
      · right
        intro x hx
        change lineDerivWithin ℝ _ D x _ = 0
        rw [← hl₀,lineDerivWithin_congr' (passiveOriginal_injected_partial e f O hO D hD hDO l₀) hx,
          lineDerivWithin_of_isOpen hD hx]
        simp only [lineDeriv,Function.comp_apply,map_add,map_smul,
          passiveOriginalInjectedProjection_single_outside e i hi,smul_zero,add_zero]
        exact deriv_const _ _
    · right
      intro x hx
      change lineDerivWithin ℝ _ D x _ = 0
      rw [lineDerivWithin_congr' hz hx,lineDerivWithin_of_isOpen hD hx]
      exact deriv_const _ _

theorem passiveOriginal_injected_paperCoordinateCj_le
    (e : Fin a ↪ Fin b) (he : StrictMono e) (j : ℕ)
    (f : (Fin a → ℝ) → Fin q → ℝ) (O S : Set (Fin a → ℝ)) (hO : IsOpen O)
    (D T : Set (Fin b → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalInjectedProjection e) D O)
    (hTD : T ⊆ D) (hTS : MapsTo (passiveOriginalInjectedProjection e) T S) :
    paperCoordinateCj j (f ∘ passiveOriginalInjectedProjection e) D T ≤
      paperCoordinateCj j f O S := by
  unfold paperCoordinateCj
  refine iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  change ENNReal.ofReal ‖paperCoordinatePartial l.val
    ((fun y => f y c) ∘ passiveOriginalInjectedProjection e) D x.val‖ ≤ _
  rcases passiveOriginal_injected_word e (fun y => f y c) O hO D hD hDO l.val with ⟨l₀,hl₀⟩ | hz
  · have hp : l₀.Pairwise (· ≤ ·) :=
      List.Pairwise.of_map e (fun i k h => le_of_not_gt (fun hki => (not_le_of_gt (he hki)) h))
        (hl₀.symm ▸ l.property.1)
    have hlen : l₀.length ≤ j := by
      simpa only [← hl₀,List.length_map] using l.property.2
    rw [← hl₀,passiveOriginal_injected_partial e (fun y => f y c) O hO D hD hDO l₀ (hTD x.property)]
    exact le_iSup_of_le ⟨l₀,hp,hlen⟩
      (le_iSup_of_le ⟨passiveOriginalInjectedProjection e x,hTS x.property⟩ (le_iSup_of_le c le_rfl))
  · rw [hz (hTD x.property)]
    simp only [norm_zero,ENNReal.ofReal_zero]
    exact bot_le

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_injected_paperCoordinateCj_le
