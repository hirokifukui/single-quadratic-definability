/-
  CommonSlopeCompiler.lean — s58.  GPT R46 Packets C1–C4 (GATE28): the reverse compiler.  A common integer slope
  `f (a + M t) = f a + B t` and the finite residue table `β ρ = f ρ` are encoded by ONE integer polynomial of total
  degree ≤ 2 (the reviewer's (V1)); no TCER, no condition on m.

  * `int_mul_sub_one_nonneg`, `oneHot_iff`, `oneHot_nonBoolean_control` (C1) — the Boolean term forces an integer
    one-hot vector inside one non-negative quadratic.
  * `slopeEncoder` (C2, data), `slopeEncoder_totalDegree`, `slopeEncoder_eval`; helper `slopeEncoder_zero_iff`.
  * `slopeEncoder_graph_iff`, `slopeEncoder_witness_unique` (C3).
  * `singleQuadratic_of_poly`, `singleQuadratic_of_commonSlope_witnesses`, `singleQuadratic_of_commonSlope` (C4) — the
    ORIGINAL sealed predicate, with `n + Mⁿ` witnesses (upper bound only).

  Statements frozen before proof (`~/lean/s58_evidence/freeze/G2_FREEZE_s58.lean`, ruling of Dr. Fukui
  2026-09-26 13:07).  Claim tags: all [P] (std-3).  One-hot penalties are a known ingredient (QUBO encodings); the
  construction is not claimed as new.
-/
import ResearchUpgrade.FamilySealedBridge
import ResearchUpgrade.ConstResidual

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

/-- **C1, the Boolean term.**  `x (x − 1) ≥ 0` on the integers. -/
theorem int_mul_sub_one_nonneg (x : ℤ) : 0 ≤ x * (x - 1) := by
  rcases le_or_gt x 0 with h | h
  · have h1 : x - 1 ≤ 0 := by linarith
    nlinarith
  · have h1 : 0 ≤ x - 1 := by omega
    nlinarith

/-- **C1.**  One non-negative quadratic forces an integer one-hot vector. -/
theorem oneHot_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℤ) :
    ((∑ i, e i) - 1) ^ 2 + ∑ i, e i * (e i - 1) = 0 ↔ ∃ i₀, e = Pi.single i₀ 1 := by
  constructor
  · intro h
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ e i * (e i - 1) :=
      fun i _ => int_mul_sub_one_nonneg (e i)
    have hs : 0 ≤ ∑ i, e i * (e i - 1) := Finset.sum_nonneg hnn
    have hsq : 0 ≤ ((∑ i, e i) - 1) ^ 2 := sq_nonneg _
    have h1 : ((∑ i, e i) - 1) ^ 2 = 0 := by linarith
    have h2 : ∑ i, e i * (e i - 1) = 0 := by linarith
    have hsum : ∑ i, e i = 1 := by
      have := (pow_eq_zero_iff two_ne_zero).mp h1
      linarith
    have hb : ∀ i, e i = 0 ∨ e i = 1 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have hex : ∃ i₀, e i₀ = 1 := by
      by_contra hne
      simp only [not_exists] at hne
      have h0 : ∀ i, e i = 0 := fun i => (hb i).resolve_right (hne i)
      simp [h0] at hsum
    obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨i₀, funext fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; simp [hi₀]
    · rcases hb i with h0 | h1'
      · simp [hi, h0]
      · exfalso
        have hnn0 : ∀ j ∈ (Finset.univ : Finset ι), j ∉ ({i₀, i} : Finset ι) → 0 ≤ e j :=
          fun j _ _ => by rcases hb j with h | h <;> omega
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i₀, i} : Finset ι)) hnn0
        rw [Finset.sum_pair (Ne.symm hi), hi₀, h1'] at hle
        omega
  · rintro ⟨i₀, rfl⟩
    have h1 : ∑ i, (Pi.single i₀ (1 : ℤ) : ι → ℤ) i = 1 := by simp
    have h2 : ∑ i, (Pi.single i₀ (1 : ℤ) : ι → ℤ) i * ((Pi.single i₀ (1 : ℤ) : ι → ℤ) i - 1) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i = i₀
      · subst hi; simp
      · simp [hi]
    rw [h1, h2]; norm_num

/-- **C1, control.**  e = (−1, 2) has sum 1 but is not Boolean; the correction term rejects it (value 4). -/
theorem oneHot_nonBoolean_control :
    (∑ i, (![-1, 2] : Fin 2 → ℤ) i) = 1 ∧
      ((∑ i, (![-1, 2] : Fin 2 → ℤ) i) - 1) ^ 2
        + ∑ i, (![-1, 2] : Fin 2 → ℤ) i * ((![-1, 2] : Fin 2 → ℤ) i - 1) = 4 := by
  constructor <;> norm_num [Fin.sum_univ_two]

/-- **C2, the encoder (V1).**  Variables: inputs `a` and outputs `b` in the sealed order `Fin (n + m)` (inputs first),
witnesses `u : Fin n` and one indicator `e ρ` per residue `ρ : Fin n → Fin M`.  With `δ ρ = M β ρ − B ρ`:
`(Σ e − 1)² + Σ e (e − 1) + ‖a − M u − Σ ρ e‖² + ‖M b − B a − Σ δ e‖²`.  Every square is of a linear form. -/
noncomputable def slopeEncoder {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) :
    MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ :=
  let aV : Fin n → MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ :=
    fun i => X (Sum.inl (Fin.castAdd m i))
  let bV : Fin m → MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ :=
    fun j => X (Sum.inl (Fin.natAdd n j))
  let uV : Fin n → MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ :=
    fun i => X (Sum.inr (Sum.inl i))
  let eV : (Fin n → Fin M) → MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ :=
    fun ρ => X (Sum.inr (Sum.inr ρ))
  let δ : (Fin n → Fin M) → Fin m → ℤ :=
    fun ρ j => (M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)
  ((∑ ρ, eV ρ) - 1) ^ 2 + ∑ ρ, eV ρ * (eV ρ - 1)
    + ∑ i, (aV i - C (M : ℤ) * uV i - ∑ ρ, C (((ρ i : ℕ) : ℤ)) * eV ρ) ^ 2
    + ∑ j, (C (M : ℤ) * bV j - ∑ i, C (B j i) * aV i - ∑ ρ, C (δ ρ j) * eV ρ) ^ 2

section degree

variable {σ : Type*}

theorem sc_td_X (i : σ) : (X i : MvPolynomial σ ℤ).totalDegree ≤ 1 := (totalDegree_X i).le

theorem sc_td_CX (c : ℤ) (i : σ) : (C c * X i : MvPolynomial σ ℤ).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 := totalDegree_C (σ := σ) c
  have h2 := sc_td_X (σ := σ) i
  omega

theorem sc_td_sub {p q : MvPolynomial σ ℤ} {k : ℕ} (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ k) :
    (p - q).totalDegree ≤ k :=
  le_trans (totalDegree_sub _ _) (max_le hp hq)

theorem sc_td_add {p q : MvPolynomial σ ℤ} {k : ℕ} (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ k) :
    (p + q).totalDegree ≤ k :=
  le_trans (totalDegree_add _ _) (max_le hp hq)

theorem sc_td_sum {ι : Type*} [Fintype ι] (g : ι → MvPolynomial σ ℤ) {k : ℕ}
    (h : ∀ x, (g x).totalDegree ≤ k) : (∑ x, g x).totalDegree ≤ k :=
  le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun x _ => h x)

theorem sc_td_sq {p : MvPolynomial σ ℤ} (h : p.totalDegree ≤ 1) : (p ^ 2).totalDegree ≤ 2 := by
  refine le_trans (totalDegree_pow _ _) ?_
  omega

theorem sc_td_one : (1 : MvPolynomial σ ℤ).totalDegree ≤ 1 := by simp

end degree

/-- **C2, degree.** -/
theorem slopeEncoder_totalDegree {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) : (slopeEncoder M B β).totalDegree ≤ 2 := by
  dsimp only [slopeEncoder]
  refine sc_td_add (sc_td_add (sc_td_add ?_ ?_) ?_) ?_
  · exact sc_td_sq (sc_td_sub (sc_td_sum _ fun ρ => sc_td_X _) sc_td_one)
  · refine sc_td_sum _ fun ρ => le_trans (totalDegree_mul _ _) ?_
    have h1 := sc_td_X (σ := Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) (Sum.inr (Sum.inr ρ))
    have h2 := sc_td_sub h1 (sc_td_one (σ := Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))))
    omega
  · exact sc_td_sum _ fun i =>
      sc_td_sq (sc_td_sub (sc_td_sub (sc_td_X _) (sc_td_CX _ _)) (sc_td_sum _ fun ρ => sc_td_CX _ _))
  · exact sc_td_sum _ fun j =>
      sc_td_sq (sc_td_sub (sc_td_sub (sc_td_CX _ _) (sc_td_sum _ fun i => sc_td_CX _ _))
        (sc_td_sum _ fun ρ => sc_td_CX _ _))

/-- **C2, evaluation.**  At every integer point the encoder is the explicit expression (V1). -/
theorem slopeEncoder_eval {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β)
      = ((∑ ρ, e ρ) - 1) ^ 2 + ∑ ρ, e ρ * (e ρ - 1)
        + ∑ i, (a i - (M : ℤ) * u i - ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ) ^ 2
        + ∑ j, ((M : ℤ) * b j - ∑ i, B j i * a i
            - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ) ^ 2 := by
  simp only [slopeEncoder, map_add, map_sub, map_sum, map_mul, map_pow, map_one, eval_X, eval_C,
    Sum.elim_inl, Sum.elim_inr, pairVec_left, pairVec_right]

/-- **C3, helper.**  The zeros of the encoder, read off term by term. -/
theorem slopeEncoder_zero_iff {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0 ↔
      ∃ ρ : Fin n → Fin M, e = Pi.single ρ 1 ∧ (∀ i, a i = (M : ℤ) * u i + ((ρ i : ℕ) : ℤ)) ∧
        ∀ j, (M : ℤ) * b j
          = ∑ i, B j i * a i + ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) := by
  classical
  rw [slopeEncoder_eval]
  have h1 : 0 ≤ ((∑ ρ, e ρ) - 1) ^ 2 + ∑ ρ, e ρ * (e ρ - 1) :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun ρ _ => int_mul_sub_one_nonneg _)
  have h2 : 0 ≤ ∑ i, (a i - (M : ℤ) * u i - ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : 0 ≤ ∑ j, ((M : ℤ) * b j - ∑ i, B j i * a i
      - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · intro h
    have hS1 : ((∑ ρ, e ρ) - 1) ^ 2 + ∑ ρ, e ρ * (e ρ - 1) = 0 := by linarith
    have hS2 : ∑ i, (a i - (M : ℤ) * u i - ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ) ^ 2 = 0 := by linarith
    have hS3 : ∑ j, ((M : ℤ) * b j - ∑ i, B j i * a i
        - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ) ^ 2 = 0 := by linarith
    obtain ⟨ρ, rfl⟩ := (oneHot_iff e).mp hS1
    refine ⟨ρ, rfl, fun i => ?_, fun j => ?_⟩
    · have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hS2 i (Finset.mem_univ _)
      have h0' := (pow_eq_zero_iff two_ne_zero).mp h0
      simp [Pi.single_apply] at h0'
      linarith
    · have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hS3 j (Finset.mem_univ _)
      have h0' := (pow_eq_zero_iff two_ne_zero).mp h0
      simp [Pi.single_apply] at h0'
      linarith
  · rintro ⟨ρ, rfl, ha, hb⟩
    have e1 := (oneHot_iff (Pi.single ρ (1 : ℤ) : (Fin n → Fin M) → ℤ)).mpr ⟨ρ, rfl⟩
    have e2 : ∀ i, a i - (M : ℤ) * u i
        - ∑ ρ', ((ρ' i : ℕ) : ℤ) * (Pi.single ρ (1 : ℤ) : (Fin n → Fin M) → ℤ) ρ' = 0 := by
      intro i; simp [Pi.single_apply]; linarith [ha i]
    have e3 : ∀ j, (M : ℤ) * b j - ∑ i, B j i * a i
        - ∑ ρ', ((M : ℤ) * β ρ' j - ∑ i, B j i * ((ρ' i : ℕ) : ℤ))
          * (Pi.single ρ (1 : ℤ) : (Fin n → Fin M) → ℤ) ρ' = 0 := by
      intro j; simp [Pi.single_apply]; linarith [hb j]
    rw [e1]
    simp only [e2, e3]
    simp

/-- **C3.**  With a common slope and the residue table `β ρ = f ρ`, the encoder defines exactly the graph of `f`. -/
theorem slopeEncoder_graph_iff {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (M : ℕ)
    (B : Matrix (Fin m) (Fin n) ℤ) (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t)
    (a : Fin n → ℤ) (b : Fin m → ℤ) :
    b = f a ↔ ∃ (u : Fin n → ℤ) (e : (Fin n → Fin M) → ℤ),
      MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e))
        (slopeEncoder M B (fun ρ => f (fun i => ((ρ i : ℕ) : ℤ)))) = 0 := by
  classical
  have hMpos : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsum : ∀ (ρ : Fin n → Fin M) (u : Fin n → ℤ),
      (∀ i, a i = (M : ℤ) * u i + ((ρ i : ℕ) : ℤ)) → ∀ j,
        ∑ i, B j i * a i = (M : ℤ) * (B *ᵥ u) j + ∑ i, B j i * ((ρ i : ℕ) : ℤ) := by
    intro ρ u ha j
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [ha i]; ring
  have hsplit : ∀ (ρ : Fin n → Fin M) (u : Fin n → ℤ),
      (∀ i, a i = (M : ℤ) * u i + ((ρ i : ℕ) : ℤ)) →
        f a = f (fun i => ((ρ i : ℕ) : ℤ)) + B *ᵥ u := by
    intro ρ u ha
    have : a = (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • u := by
      funext i; simp [ha i]; ring
    rw [this, hcs]
  constructor
  · rintro rfl
    let ρ : Fin n → Fin M := fun i =>
      ⟨(a i % M).toNat, by
        have h1 := Int.emod_lt_of_pos (a i) hMpos
        have h2 := Int.emod_nonneg (a i) (ne_of_gt hMpos)
        omega⟩
    have hρ : ∀ i, ((ρ i : ℕ) : ℤ) = a i % M := fun i =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMpos))
    have ha : ∀ i, a i = (M : ℤ) * (a i / M) + ((ρ i : ℕ) : ℤ) := by
      intro i; rw [hρ i]; have := Int.emod_add_ediv (a i) (M : ℤ); linarith
    refine ⟨fun i => a i / M, Pi.single ρ 1, (slopeEncoder_zero_iff _ _ _ _ _ _ _).mpr ⟨ρ, rfl, ha, fun j => ?_⟩⟩
    rw [hsplit ρ _ ha, hsum ρ _ ha j]
    simp only [Pi.add_apply]
    ring
  · rintro ⟨u, e, h0⟩
    obtain ⟨ρ, -, ha, hb⟩ := (slopeEncoder_zero_iff _ _ _ _ _ _ _).mp h0
    rw [hsplit ρ u ha]
    funext j
    have h := hb j
    rw [hsum ρ u ha j] at h
    have hM0 : (M : ℤ) ≠ 0 := ne_of_gt hMpos
    simp only [Pi.add_apply]
    apply mul_left_cancel₀ hM0
    linarith

/-- **C3, witness uniqueness of the encoder.** -/
theorem slopeEncoder_witness_unique {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (hM : 1 ≤ M) {a : Fin n → ℤ} {b : Fin m → ℤ}
    {u u' : Fin n → ℤ} {e e' : (Fin n → Fin M) → ℤ}
    (h : MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0)
    (h' : MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u' e')) (slopeEncoder M B β) = 0) :
    u = u' ∧ e = e' := by
  classical
  have hMpos : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨ρ, rfl, ha, -⟩ := (slopeEncoder_zero_iff _ _ _ _ _ _ _).mp h
  obtain ⟨ρ', rfl, ha', -⟩ := (slopeEncoder_zero_iff _ _ _ _ _ _ _).mp h'
  have key : ∀ i, u i = u' i ∧ ((ρ i : ℕ) : ℤ) = ((ρ' i : ℕ) : ℤ) := by
    intro i
    have r1 : a i / M = u i ∧ a i % M = ((ρ i : ℕ) : ℤ) :=
      (Int.ediv_emod_unique hMpos).mpr ⟨by linarith [ha i], by positivity, by exact_mod_cast (ρ i).isLt⟩
    have r2 : a i / M = u' i ∧ a i % M = ((ρ' i : ℕ) : ℤ) :=
      (Int.ediv_emod_unique hMpos).mpr ⟨by linarith [ha' i], by positivity, by exact_mod_cast (ρ' i).isLt⟩
    exact ⟨r1.1.symm.trans r2.1, r1.2.symm.trans r2.2⟩
  have hρ : ρ = ρ' := funext fun i => Fin.ext (by exact_mod_cast (key i).2)
  exact ⟨funext fun i => (key i).1, by rw [hρ]⟩

/-- **C4, helper.**  A degree-≤2 polynomial over ANY finite witness type defining the graph gives the sealed predicate. -/
theorem singleQuadratic_of_poly {n m : ℕ} {W : Type} [Fintype W]
    (P : MvPolynomial (Fin (n + m) ⊕ W) ℤ) (hP : P.totalDegree ≤ 2) (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : ∀ (a : Fin n → ℤ) (b : Fin m → ℤ),
      b = f a ↔ ∃ w : W → ℤ, MvPolynomial.eval (Sum.elim (pairVec a b) w) P = 0) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by
  classical
  let eqv := Fintype.equivFin W
  refine ⟨Fintype.card W, MvPolynomial.rename (Sum.map id eqv) P,
    le_trans (MvPolynomial.totalDegree_rename_le _ _) hP, ?_⟩
  intro v
  have hv : ∀ y : Fin (Fintype.card W) → ℤ,
      DiophCompression.evalAtZZ (MvPolynomial.rename (Sum.map id eqv) P) v y
        = MvPolynomial.eval (Sum.elim v (y ∘ eqv)) P := by
    intro y
    unfold DiophCompression.evalAtZZ
    rw [MvPolynomial.eval_rename]
    have hx : (Sum.elim v y) ∘ (Sum.map id eqv) = Sum.elim v (y ∘ eqv) := by
      funext x; rcases x with x | w <;> rfl
    rw [hx]
  have hvp : v = pairVec (fun i => v (Fin.castAdd m i)) (fun j => v (Fin.natAdd n j)) := by
    funext k
    induction k using Fin.addCases with
    | left i => simp
    | right j => simp
  show (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i)) ↔ _
  rw [h, ← hvp]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ eqv.symm, ?_⟩
    have hc : (w ∘ eqv.symm) ∘ eqv = w := by funext x; simp
    rw [hv, hc]; exact hw
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ eqv, by rw [hv] at hy; exact hy⟩

/-- **C4, with the witness count.**  A common slope of modulus `M` gives a sealed representation with `n + Mⁿ`
witnesses (an upper bound; no minimality is claimed). -/
theorem singleQuadratic_of_commonSlope_witnesses {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (M : ℕ)
    (B : Matrix (Fin m) (Fin n) ℤ) (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    ∃ P : MvPolynomial (Fin (n + m) ⊕ Fin (n + M ^ n)) ℤ, P.totalDegree ≤ 2 ∧
      ∀ v : Fin (n + m) → ℤ, v ∈ DiophCompression.graphVecZZ f ↔
        ∃ y : Fin (n + M ^ n) → ℤ, MvPolynomial.eval (Sum.elim v y) P = 0 := by
  classical
  have hcard : Fintype.card (Fin n ⊕ (Fin n → Fin M)) = n + M ^ n := by
    simp [Fintype.card_sum, Fintype.card_fun]
  let eqv : (Fin n ⊕ (Fin n → Fin M)) ≃ Fin (n + M ^ n) := Fintype.equivFinOfCardEq hcard
  let P := slopeEncoder M B (fun ρ => f (fun i => ((ρ i : ℕ) : ℤ)))
  refine ⟨MvPolynomial.rename (Sum.map id eqv) P,
    le_trans (MvPolynomial.totalDegree_rename_le _ _) (slopeEncoder_totalDegree _ _ _), fun v => ?_⟩
  have hv : ∀ y : Fin (n + M ^ n) → ℤ,
      MvPolynomial.eval (Sum.elim v y) (MvPolynomial.rename (Sum.map id eqv) P)
        = MvPolynomial.eval (Sum.elim v (y ∘ eqv)) P := by
    intro y
    rw [MvPolynomial.eval_rename]
    have hx : (Sum.elim v y) ∘ (Sum.map id eqv) = Sum.elim v (y ∘ eqv) := by
      funext x; rcases x with x | w <;> rfl
    rw [hx]
  have hvp : v = pairVec (fun i => v (Fin.castAdd m i)) (fun j => v (Fin.natAdd n j)) := by
    funext k
    induction k using Fin.addCases with
    | left i => simp
    | right j => simp
  show (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i)) ↔ _
  rw [slopeEncoder_graph_iff M B hM hcs, ← hvp]
  constructor
  · rintro ⟨u, e, h0⟩
    refine ⟨(Sum.elim u e) ∘ eqv.symm, ?_⟩
    have hc : ((Sum.elim u e) ∘ eqv.symm) ∘ eqv = Sum.elim u e := by funext x; simp
    rw [hv, hc]; exact h0
  · rintro ⟨y, hy⟩
    refine ⟨fun i => y (eqv (Sum.inl i)), fun ρ => y (eqv (Sum.inr ρ)), ?_⟩
    rw [hv] at hy
    have hc : (y ∘ eqv) = Sum.elim (fun i => y (eqv (Sum.inl i))) (fun ρ => y (eqv (Sum.inr ρ))) := by
      funext x; rcases x with i | ρ <;> rfl
    rw [hc] at hy
    exact hy

/-- **C4.**  Common slope ⇒ the ORIGINAL sealed predicate (unconditional, every `n, m`). -/
theorem singleQuadratic_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) : DiophCompression.SingleQuadraticDefinableFunctionZZ f := by
  obtain ⟨M, B, hM, hcs⟩ := h
  obtain ⟨P, hP, hrep⟩ := singleQuadratic_of_commonSlope_witnesses M B hM hcs
  exact ⟨n + M ^ n, P, hP, fun v => hrep v⟩

end DiophCompression.ResearchUpgrade
