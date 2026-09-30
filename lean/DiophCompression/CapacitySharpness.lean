/-
  DiophCompression/CapacitySharpness.lean — r04 Task 2 (sharpness) + Task 3 (exact S(d,q)),
  session 4, 2026-08-26, claude.ai direct.
  * degree profile e : Fin m → ℕ: an injective polynomial map ℕ^{Σe} → ℤ^m with deg F_j ≤ e_j
    (independent Skolem tupling per block), hence max n = Σ e_j together with Task 1.
  * S(d, q) ≥ C(d+q, q+1): one Skolem block of size d−|m| in each coefficient slot z^m, |m| ≤ d.
-/
import DiophCompression.SkolemTupling
import DiophCompression.SpecializationCapacity
import DiophCompression.PolynomialMapCapacity

namespace DiophCompression

open MvPolynomial

/-- `aeval` along constants is `C` of the evaluation. -/
theorem aeval_C_comp {σ τ : Type} (h : σ → ℤ) (p : MvPolynomial σ ℤ) :
    aeval (fun i => (C (h i) : MvPolynomial τ ℤ)) p = C (eval h p) := by
  rw [aeval_def, algebraMap_eq, eval, coe_eval₂Hom, eval₂_comp_left C (RingHom.id ℤ) h p]
  rfl

/-! ### Degree-profile sharpness -/

/-- Block embedding of the `j`-th block of size `e j` into `Fin (Σ e)`. -/
def blockEmb {m : ℕ} (e : Fin m → ℕ) (j : Fin m) (i : Fin (e j)) : Fin (∑ j, e j) :=
  finSigmaFinEquiv ⟨j, i⟩

/-- The sharp injective polynomial map: Skolem tupling on each block. -/
noncomputable def sharpMap {m : ℕ} (e : Fin m → ℕ) (j : Fin m) : MvPolynomial (Fin (∑ j, e j)) ℤ :=
  rename (blockEmb e j) (skolemPoly (e j))

theorem sharpMap_totalDegree {m : ℕ} (e : Fin m → ℕ) (j : Fin m) :
    (sharpMap e j).totalDegree ≤ e j :=
  le_trans (totalDegree_rename_le _ _) (skolemPoly_totalDegree _)

theorem sharpMap_injective {m : ℕ} (e : Fin m → ℕ) : Function.Injective (polyMap (sharpMap e)) := by
  intro a a' haa
  have hblock : ∀ j, (fun i => a (blockEmb e j i)) = (fun i => a' (blockEmb e j i)) := by
    intro j
    apply skolemPoly_injective (e j)
    have hj := congrFun haa j
    simp only [polyMap, sharpMap, eval_rename] at hj
    exact hj
  funext v
  obtain ⟨⟨j, i⟩, rfl⟩ := finSigmaFinEquiv.surjective v
  exact congrFun (hblock j) i

/-- SHARPNESS (Task 2): for every degree profile there is an injective polynomial map on ℕ^{Σe}. -/
theorem exists_injective_polyMap_degreeSum {m : ℕ} (e : Fin m → ℕ) :
    ∃ F : Fin m → MvPolynomial (Fin (∑ j, e j)) ℤ,
      (∀ j, (F j).totalDegree ≤ e j) ∧ Function.Injective (polyMap F) :=
  ⟨sharpMap e, sharpMap_totalDegree e, sharpMap_injective e⟩

/-- EXACT degree-profile capacity (Task 2 pass condition): max n = Σ e_j, both directions. -/
theorem degreeProfile_capacity_exact {m : ℕ} (e : Fin m → ℕ) :
    (∀ (n : ℕ) (F : Fin m → MvPolynomial (Fin n) ℤ), (∀ j, (F j).totalDegree ≤ e j) →
        Function.Injective (polyMap F) → n ≤ ∑ j, e j) ∧
    (∃ F : Fin m → MvPolynomial (Fin (∑ j, e j)) ℤ,
        (∀ j, (F j).totalDegree ≤ e j) ∧ Function.Injective (polyMap F)) :=
  ⟨fun _ F he hinj => injective_polyMap_dimension_le_degreeSum F e he hinj,
   exists_injective_polyMap_degreeSum e⟩

/-! ### Exact specialization capacity S(d, q) = C(d+q, q+1) -/

section Spec
variable (d q : ℕ)

/-- Enumerate the exponent vectors of degree ≤ d. -/
noncomputable def slot : Fin (degLE d q).card → (Fin q → ℕ) :=
  fun k => ((degLE d q).equivFin.symm k).1

theorem slot_injective : Function.Injective (slot d q) := by
  intro k k' h
  exact (degLE d q).equivFin.symm.injective (Subtype.ext h)

theorem slot_mem (k : Fin (degLE d q).card) : slot d q k ∈ degLE d q :=
  ((degLE d q).equivFin.symm k).2

/-- Block sizes: d − |m| for each slot. -/
noncomputable def slotW : Fin (degLE d q).card → ℕ := fun k => d - ∑ j, slot d q k j

theorem sum_slotW : ∑ k, slotW d q k = (d + q).choose (q + 1) := by
  rw [← wCount_eq_choose']
  unfold wCount slotW slot
  rw [← Finset.sum_coe_sort (degLE d q) (fun m => d - ∑ j, m j)]
  exact Equiv.sum_comp (degLE d q).equivFin.symm (fun m => d - ∑ j, m.1 j)

/-- The exponent finsupp of slot `k`. -/
noncomputable def slotMono (k : Fin (degLE d q).card) : Fin q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (slot d q k)

theorem slotMono_injective : Function.Injective (slotMono d q) := by
  intro k k' h
  exact slot_injective d q (Finsupp.equivFunOnFinite.symm.injective h)

/-- The sharp specialization polynomial: Σ_k skolem(block_k) · z^{slot k}. -/
noncomputable def sharpSpec : MvPolynomial (Fin (∑ k, slotW d q k) ⊕ Fin q) ℤ :=
  ∑ k, rename (Sum.inl ∘ blockEmb (slotW d q) k) (skolemPoly (slotW d q k))
        * rename Sum.inr (monomial (slotMono d q k) 1)

theorem sharpSpec_totalDegree : (sharpSpec d q).totalDegree ≤ d := by
  unfold sharpSpec
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le ?_)
  intro k _
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 : (rename ((Sum.inl : Fin (∑ k, slotW d q k) → Fin (∑ k, slotW d q k) ⊕ Fin q)
      ∘ blockEmb (slotW d q) k) (skolemPoly (slotW d q k))).totalDegree
      ≤ slotW d q k := le_trans (totalDegree_rename_le _ _) (skolemPoly_totalDegree _)
  have h2 : (rename (Sum.inr : Fin q → Fin (∑ k, slotW d q k) ⊕ Fin q)
      (monomial (slotMono d q k) (1 : ℤ))).totalDegree ≤ ∑ j, slot d q k j := by
    refine le_trans (totalDegree_rename_le _ _) (le_trans (totalDegree_monomial_le _ _) ?_)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact le_of_eq rfl
  have h3 : ∑ j, slot d q k j ≤ d := mem_degLE.1 (slot_mem d q k)
  have hw : slotW d q k = d - ∑ j, slot d q k j := rfl
  omega

theorem specialize_sharpSpec (a : Fin (∑ k, slotW d q k) → ℕ) :
    specialize (sharpSpec d q) a
      = ∑ k, C (eval (fun i => (a (blockEmb (slotW d q) k i) : ℤ)) (skolemPoly (slotW d q k)))
          * monomial (slotMono d q k) 1 := by
  unfold sharpSpec specialize
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, aeval_rename, aeval_rename]
  congr 1
  · have : (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X ∘ (Sum.inl ∘ blockEmb (slotW d q) k))
        = fun i => (C ((a (blockEmb (slotW d q) k i) : ℕ) : ℤ) : MvPolynomial (Fin q) ℤ) := by
      funext i; rfl
    rw [this, aeval_C_comp]
  · have : (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X ∘ (Sum.inr : Fin q → _)) = X := by
      funext j; rfl
    rw [this, aeval_X_left]; rfl

theorem coeff_specialize_sharpSpec (a : Fin (∑ k, slotW d q k) → ℕ) (k : Fin (degLE d q).card) :
    coeff (slotMono d q k) (specialize (sharpSpec d q) a)
      = eval (fun i => (a (blockEmb (slotW d q) k i) : ℤ)) (skolemPoly (slotW d q k)) := by
  classical
  rw [specialize_sharpSpec, coeff_sum]
  have : ∀ k' ∈ (Finset.univ : Finset (Fin (degLE d q).card)),
      coeff (slotMono d q k)
        (C (eval (fun i => (a (blockEmb (slotW d q) k' i) : ℤ)) (skolemPoly (slotW d q k')))
          * monomial (slotMono d q k') (1 : ℤ))
        = if k' = k then
            eval (fun i => (a (blockEmb (slotW d q) k i) : ℤ)) (skolemPoly (slotW d q k)) else 0 := by
    intro k' _
    rw [coeff_C_mul, coeff_monomial]
    by_cases h : k' = k
    · subst h; simp
    · have : slotMono d q k' ≠ slotMono d q k := fun h' => h (slotMono_injective d q h')
      simp [this, h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp

theorem sharpSpec_injective : Function.Injective (specialize (sharpSpec d q)) := by
  intro a a' haa
  have hblock : ∀ k, (fun i => a (blockEmb (slotW d q) k i)) = (fun i => a' (blockEmb (slotW d q) k i)) := by
    intro k
    apply skolemPoly_injective (slotW d q k)
    have := coeff_specialize_sharpSpec d q a k
    rw [haa, coeff_specialize_sharpSpec d q a' k] at this
    exact this.symm
  funext v
  obtain ⟨⟨k, i⟩, rfl⟩ := finSigmaFinEquiv.surjective v
  exact congrFun (hblock k) i

/-- S(d, q) ≥ C(d+q, q+1): the sharp specialization is achievable. -/
theorem specialization_achievable_choose : SpecializationAchievable ((d + q).choose (q + 1)) q d := by
  rw [← sum_slotW]
  exact ⟨sharpSpec d q, sharpSpec_totalDegree d q, sharpSpec_injective d q⟩

/-- EXACT SPECIALIZATION CAPACITY (Task 3): S(d, q) = C(d+q, q+1), both directions. -/
theorem specialization_capacity_exact :
    (∀ n, SpecializationAchievable n q d → n ≤ (d + q).choose (q + 1)) ∧
    SpecializationAchievable ((d + q).choose (q + 1)) q d :=
  ⟨fun _ h => specialization_bound h, specialization_achievable_choose d q⟩

end Spec

end DiophCompression

#print axioms DiophCompression.degreeProfile_capacity_exact
#print axioms DiophCompression.specialization_achievable_choose
#print axioms DiophCompression.specialization_capacity_exact
