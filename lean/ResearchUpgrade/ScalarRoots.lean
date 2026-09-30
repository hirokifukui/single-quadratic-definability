/-
  ScalarRoots.lean — s59.  GPT R47 Packets B3, B4, C1–C3 (GATE29): the witness-free scalar relation
  `a y² + (β·x + d) y + (xᵀEx + φ·x + g) = 0` that is the graph of a total function F : ℤⁿ → ℤ.  No TCER.

  * `ParityAffineNF` (family H) — F = (p·x + c)/2 where that numerator is even, (q·x + c')/2 elsewhere, with
    p ≡ q (mod 2), p ≢ 0 (mod 2), c − c' odd.
  * `affine_dvd_iff_sub`, `affine_dvd_add_smul`, `affine_eq_of_eq_on_coset` (C1) — integrality domains of integer affine
    forms are cosets containing full cosets x + kℤⁿ; agreement on a full coset forces equality.
  * `addSubgroup_two_coset_cover` (C2) — a subgroup and a coset of a subgroup that partition an additive commutative
    group are cosets of ONE subgroup of index two (no finiteness, no density).
  * `rn_two_roots` (B4) — a ≠ 0: the relation is "2a·y is one of two integer affine values".
  * `globalQuadratic_of_rn_zero` (B3), `rn_classify` (C3) — F is one global rational quadratic or parity-affine.
    Helper `globalQuadratic_of_int_affine` (added during the proof, not in the freeze).
  * `parityFn_parityAffine`; controls `plusMinus_not_relUnique`, `sameParity_not_function`, `modThree_not_total`.

  Statements frozen before proof (`~/lean/s59_evidence/freeze/H1_FREEZE_s59.lean` fbb986ed, ruling of Dr. Fukui
  2026-09-27 15:56).  Claim tags: all [P] (std-3).  The route (two roots, index-two covering) follows GPT R47
  SCALAR_CLASSIFICATION_ROUTE §§3–7; novelty is not claimed here.
-/
import ResearchUpgrade.NInputNoWitness
import ResearchUpgrade.VectorClassification

namespace DiophCompression.ResearchUpgrade

open Matrix

def ParityAffineNF {n : ℕ} (F : (Fin n → ℤ) → ℤ) : Prop :=
  ∃ (p q : Fin n → ℤ) (c c' : ℤ), (∀ i, (2 : ℤ) ∣ p i - q i) ∧ (∃ i, ¬ (2 : ℤ) ∣ p i) ∧ ¬ (2 : ℤ) ∣ c - c' ∧
    ∀ x : Fin n → ℤ, ((2 : ℤ) ∣ p ⬝ᵥ x + c → 2 * F x = p ⬝ᵥ x + c) ∧
      (¬ (2 : ℤ) ∣ p ⬝ᵥ x + c → 2 * F x = q ⬝ᵥ x + c')

theorem affine_dvd_iff_sub {n : ℕ} (k : ℤ) (w : Fin n → ℤ) (e : ℤ) {x₀ : Fin n → ℤ}
    (h₀ : k ∣ w ⬝ᵥ x₀ + e) (x : Fin n → ℤ) : k ∣ w ⬝ᵥ x + e ↔ k ∣ w ⬝ᵥ (x - x₀) := by
  have hx : w ⬝ᵥ x + e = (w ⬝ᵥ x₀ + e) + w ⬝ᵥ (x - x₀) := by rw [dotProduct_sub]; ring
  rw [hx]
  exact dvd_add_right h₀

theorem affine_dvd_add_smul {n : ℕ} (k : ℤ) (w : Fin n → ℤ) (e : ℤ) {x : Fin n → ℤ}
    (h : k ∣ w ⬝ᵥ x + e) (t : Fin n → ℤ) : k ∣ w ⬝ᵥ (x + k • t) + e := by
  have hx : w ⬝ᵥ (x + k • t) + e = (w ⬝ᵥ x + e) + k * (w ⬝ᵥ t) := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  rw [hx]
  exact dvd_add h (dvd_mul_right k _)

theorem affine_eq_of_eq_on_coset {n : ℕ} {k : ℤ} (hk : k ≠ 0) {w w' : Fin n → ℤ} {e e' : ℤ} (x₀ : Fin n → ℤ)
    (h : ∀ t : Fin n → ℤ, w ⬝ᵥ (x₀ + k • t) + e = w' ⬝ᵥ (x₀ + k • t) + e') : w = w' ∧ e = e' := by
  have h0 := h 0
  simp only [smul_zero, add_zero] at h0
  have hw : w = w' := by
    funext i
    have hi := h (Pi.single i 1)
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_single, dotProduct_single, mul_one, mul_one] at hi
    have hk' : k * w i = k * w' i := by linarith
    exact mul_left_cancel₀ hk hk'
  refine ⟨hw, ?_⟩
  subst hw
  linarith

theorem addSubgroup_two_coset_cover {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (b : G)
    (hcov : ∀ g : G, g ∈ H ∨ g - b ∈ K) (hdisj : ∀ g : G, g ∈ H → g - b ∉ K) :
    H = K ∧ b ∉ H ∧ (∀ g : G, g ∈ H ∨ g - b ∈ H) ∧ ∀ g : G, g + g ∈ H := by
  have hb : b ∉ H := fun hbH => hdisj b hbH (by rw [sub_self]; exact K.zero_mem)
  have hKH : ∀ k ∈ K, k ∈ H := by
    intro k hk
    by_contra hkH
    have h1 : k - b ∈ K := (hcov k).resolve_left hkH
    have hbK : b ∈ K := by
      have := K.sub_mem hk h1
      rwa [sub_sub_cancel] at this
    exact hdisj 0 H.zero_mem (by rw [zero_sub]; exact K.neg_mem hbK)
  have hHK : ∀ h ∈ H, h ∈ K := by
    intro h hh
    by_contra hhK
    have h1 : h + b ∈ H := by
      rcases hcov (h + b) with h' | h'
      · exact h'
      · exact absurd (by rwa [add_sub_cancel_right] at h') hhK
    have hbH : b ∈ H := by
      have := H.sub_mem h1 hh
      rwa [add_sub_cancel_left] at this
    exact hb hbH
  have hEq : H = K := le_antisymm (fun x hx => hHK x hx) (fun x hx => hKH x hx)
  subst hEq
  refine ⟨rfl, hb, hcov, fun g => ?_⟩
  rcases hcov g with hg | hg
  · exact H.add_mem hg hg
  · by_contra hgg
    have h1 : g + g - b ∈ H := (hcov (g + g)).resolve_left hgg
    have h2 : g ∈ H := by
      have := H.sub_mem h1 hg
      have e : g + g - b - (g - b) = g := by abel
      rwa [e] at this
    exact hgg (H.add_mem h2 h2)

theorem rn_two_roots {n : ℕ} {F : (Fin n → ℤ) → ℤ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ) (ha : a ≠ 0)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = F x) :
    ∃ (ℓ : Fin n → ℤ) (s : ℤ), ∀ (x : Fin n → ℤ) (y : ℤ),
      Rn a β d E φ g x y ↔
        (2 * a * y = -(β ⬝ᵥ x + d) + (ℓ ⬝ᵥ x + s) ∨ 2 * a * y = -(β ⬝ᵥ x + d) - (ℓ ⬝ᵥ x + s)) := by
  have hspec : ∀ x : Fin n → ℤ,
      a * F x ^ 2 + (β ⬝ᵥ x + d) * F x + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
    intro x; have h := (hF x (F x)).mpr rfl; simpa [Rn, Pn] using h
  set Am : Matrix (Fin n) (Fin n) ℤ := vecMulVec β β - (4 * a) • E with hAm
  set bv : Fin n → ℤ := (2 * d) • β - (4 * a) • φ with hbv
  set cv : ℤ := d ^ 2 - 4 * a * g with hcv
  have hw : ∀ x : Fin n → ℤ, (2 * a * F x + (β ⬝ᵥ x + d)) ^ 2 = deltaQ Am bv cv x := by
    intro x; rw [hAm, hbv, hcv, deltaQ_disc]; linear_combination (4 * a) * hspec x
  have hdisc : ∀ x : Fin n → ℤ, IsSquare (deltaQ Am bv cv x) :=
    fun x => ⟨2 * a * F x + (β ⬝ᵥ x + d), by rw [← hw x]; ring⟩
  obtain ⟨ℓ, s, hℓs⟩ := c21_affine_square Am bv cv hdisc
  have hFint : ∀ x : Fin n → ℤ, ∃ z : ℤ, (z : ℚ) = ℓ ⬝ᵥ castQ x + s := by
    intro x
    have hEq : (ℓ ⬝ᵥ castQ x + s) ^ 2 = ((2 * a * F x + (β ⬝ᵥ x + d) : ℤ) : ℚ) ^ 2 := by
      rw [← hℓs x, ← hw x]; push_cast; ring
    have hfac : (ℓ ⬝ᵥ castQ x + s - ((2 * a * F x + (β ⬝ᵥ x + d) : ℤ) : ℚ))
        * (ℓ ⬝ᵥ castQ x + s + ((2 * a * F x + (β ⬝ᵥ x + d) : ℤ) : ℚ)) = 0 := by
      linear_combination hEq
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨2 * a * F x + (β ⬝ᵥ x + d), by linarith [sub_eq_zero.1 h]⟩
    · refine ⟨-(2 * a * F x + (β ⬝ᵥ x + d)), ?_⟩; push_cast at h ⊢; linarith [h]
  obtain ⟨s', hs'0⟩ := hFint 0
  have hs' : (s' : ℚ) = s := by
    rw [hs'0]; have : ℓ ⬝ᵥ castQ (0 : Fin n → ℤ) = 0 := by simp [castQ, dotProduct]
    rw [this, zero_add]
  have hli : ∀ i, ∃ z : ℤ, (z : ℚ) = ℓ i := by
    intro i
    obtain ⟨z, hz⟩ := hFint (Pi.single i 1)
    refine ⟨z - s', ?_⟩
    have hdot : ℓ ⬝ᵥ castQ (Pi.single i (1 : ℤ)) = ℓ i := by
      have : castQ (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℚ) := by
        funext j; simp [castQ, Pi.single_apply]
      rw [this, dotProduct_single, mul_one]
    rw [hdot] at hz
    push_cast; rw [hz, hs']; ring
  choose ℓ' hℓ' using hli
  have hℚcast : ∀ x : Fin n → ℤ, ((ℓ' ⬝ᵥ x : ℤ) : ℚ) = ℓ ⬝ᵥ castQ x := by
    intro x
    simp only [dotProduct, castQ, Int.cast_sum]
    apply Finset.sum_congr rfl; intro i _; rw [← hℓ' i]; push_cast; ring
  have hΔ : ∀ x : Fin n → ℤ, deltaQ Am bv cv x = (ℓ' ⬝ᵥ x + s') ^ 2 := by
    intro x
    have hq : ((deltaQ Am bv cv x : ℤ) : ℚ) = (((ℓ' ⬝ᵥ x + s') ^ 2 : ℤ) : ℚ) := by
      rw [hℓs x, ← hℚcast x, ← hs']; push_cast; ring
    exact_mod_cast hq
  have hDsc : ∀ x : Fin n → ℤ,
      (β ⬝ᵥ x + d) ^ 2 - 4 * a * (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = (ℓ' ⬝ᵥ x + s') ^ 2 := by
    intro x; rw [← deltaQ_disc a β d E φ g x, ← hAm, ← hbv, ← hcv]; exact hΔ x
  refine ⟨ℓ', s', fun x y => ?_⟩
  have hd := hDsc x
  simp only [Rn, Pn]
  constructor
  · intro h
    have hsq : (2 * a * y + (β ⬝ᵥ x + d)) ^ 2 = (ℓ' ⬝ᵥ x + s') ^ 2 := by
      linear_combination (4 * a) * h + hd
    have hfac : (2 * a * y + (β ⬝ᵥ x + d) - (ℓ' ⬝ᵥ x + s'))
        * (2 * a * y + (β ⬝ᵥ x + d) + (ℓ' ⬝ᵥ x + s')) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfac with h1 | h1
    · left; linarith
    · right; linarith
  · intro h
    have h4 : (4 * a) * (a * y ^ 2 + (β ⬝ᵥ x + d) * y + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g)) = 0 := by
      rcases h with h | h
      · linear_combination (2 * a * y + (β ⬝ᵥ x + d) + (ℓ' ⬝ᵥ x + s')) * h - hd
      · linear_combination (2 * a * y + (β ⬝ᵥ x + d) - (ℓ' ⬝ᵥ x + s')) * h - hd
    rcases mul_eq_zero.1 h4 with hh | hh
    · exact absurd hh (by intro hz; apply ha; linarith)
    · exact hh

theorem globalQuadratic_of_rn_zero {n : ℕ} {F : (Fin n → ℤ) → ℤ} (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn 0 β d E φ g x y ↔ y = F x) : GlobalQuadratic F := by
  have hT : RelTotal (Rn 0 β d E φ g) := fun x => ⟨F x, (hF x _).mpr rfl⟩
  have hU : RelUnique (Rn 0 β d E φ g) :=
    fun x y y' hy hy' => ((hF x y).mp hy).trans ((hF x y').mp hy').symm
  have hfn : fn 0 β d E φ g hT = F := funext fun x => (hF x _).mp (Classical.choose_spec (hT x))
  rw [← hfn]
  exact n_a_zero_global 0 β d E φ g hT hU rfl

/-- Helper: `k·F = w·x + e` with `k ≠ 0` is a global rational (affine) quadratic. -/
theorem globalQuadratic_of_int_affine {n : ℕ} {F : (Fin n → ℤ) → ℤ} {k : ℤ} (hk : k ≠ 0)
    (w : Fin n → ℤ) (e : ℤ) (h : ∀ x : Fin n → ℤ, k * F x = w ⬝ᵥ x + e) : GlobalQuadratic F := by
  refine ⟨⟨(e : ℚ) / k, fun i => (w i : ℚ) / k, 0⟩, fun x => ?_⟩
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hx : (k : ℚ) * (F x : ℚ) = ((w ⬝ᵥ x : ℤ) : ℚ) + e := by exact_mod_cast h x
  have hdot : (fun i => (w i : ℚ) / k) ⬝ᵥ castQ x = ((w ⬝ᵥ x : ℤ) : ℚ) / k := by
    simp only [dotProduct, castQ, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; ring
  show (F x : ℚ) = (e : ℚ) / k + (fun i => (w i : ℚ) / k) ⬝ᵥ castQ x
    + castQ x ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℚ) *ᵥ castQ x
  rw [Matrix.zero_mulVec, dotProduct_zero, add_zero, hdot]
  have hsum : (e : ℚ) / k + ((w ⬝ᵥ x : ℤ) : ℚ) / k = (((w ⬝ᵥ x : ℤ) : ℚ) + e) / k := by ring
  rw [hsum, eq_div_iff hkQ]
  linear_combination hx

theorem rn_classify {n : ℕ} {F : (Fin n → ℤ) → ℤ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = F x) :
    GlobalQuadratic F ∨ ParityAffineNF F := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; exact Or.inl (globalQuadratic_of_rn_zero β d E φ g hF)
  obtain ⟨ℓ, s, hroot⟩ := rn_two_roots a β d E φ g ha hF
  set U : Fin n → ℤ := -β + ℓ with hUdef
  set V : Fin n → ℤ := -β - ℓ with hVdef
  set u0 : ℤ := -d + s with hu0
  set v0 : ℤ := -d - s with hv0
  have hu : ∀ x : Fin n → ℤ, -(β ⬝ᵥ x + d) + (ℓ ⬝ᵥ x + s) = U ⬝ᵥ x + u0 := by
    intro x; rw [hUdef, hu0, add_dotProduct, neg_dotProduct]; ring
  have hv : ∀ x : Fin n → ℤ, -(β ⬝ᵥ x + d) - (ℓ ⬝ᵥ x + s) = V ⬝ᵥ x + v0 := by
    intro x; rw [hVdef, hv0, sub_dotProduct, neg_dotProduct]; ring
  have h2a : (2 * a : ℤ) ≠ 0 := mul_ne_zero two_ne_zero ha
  have hsplit : ∀ x, 2 * a * F x = U ⬝ᵥ x + u0 ∨ 2 * a * F x = V ⬝ᵥ x + v0 := by
    intro x
    have h := (hroot x (F x)).mp ((hF x _).mpr rfl)
    rw [hu, hv] at h; exact h
  have hUdiv : ∀ x, 2 * a ∣ U ⬝ᵥ x + u0 → 2 * a * F x = U ⬝ᵥ x + u0 := by
    rintro x ⟨k, hk⟩
    have hR : Rn a β d E φ g x k := (hroot x k).mpr (Or.inl (by rw [hu]; linarith))
    rw [← (hF x k).mp hR]; linarith
  have hVdiv : ∀ x, 2 * a ∣ V ⬝ᵥ x + v0 → 2 * a * F x = V ⬝ᵥ x + v0 := by
    rintro x ⟨k, hk⟩
    have hR : Rn a β d E φ g x k := (hroot x k).mpr (Or.inr (by rw [hv]; linarith))
    rw [← (hF x k).mp hR]; linarith
  have hcover : ∀ x, 2 * a ∣ U ⬝ᵥ x + u0 ∨ 2 * a ∣ V ⬝ᵥ x + v0 :=
    fun x => (hsplit x).imp (fun h => ⟨F x, h.symm⟩) (fun h => ⟨F x, h.symm⟩)
  by_cases hboth : ∃ x₀, 2 * a ∣ U ⬝ᵥ x₀ + u0 ∧ 2 * a ∣ V ⬝ᵥ x₀ + v0
  · obtain ⟨x₀, h1, h2⟩ := hboth
    have heq : U = V ∧ u0 = v0 := affine_eq_of_eq_on_coset h2a x₀ (fun t => by
      rw [← hUdiv _ (affine_dvd_add_smul _ _ _ h1 t), ← hVdiv _ (affine_dvd_add_smul _ _ _ h2 t)])
    left
    refine globalQuadratic_of_int_affine h2a U u0 (fun x => ?_)
    rcases hsplit x with h | h
    · exact h
    · rw [h, heq.1, heq.2]
  push_neg at hboth
  by_cases hUe : ∃ x₀, 2 * a ∣ U ⬝ᵥ x₀ + u0
  swap
  · push_neg at hUe
    left
    refine globalQuadratic_of_int_affine h2a V v0 (fun x => ?_)
    rcases hsplit x with h | h
    · exact absurd ⟨F x, h.symm⟩ (hUe x)
    · exact h
  by_cases hVe : ∃ y₀, 2 * a ∣ V ⬝ᵥ y₀ + v0
  swap
  · push_neg at hVe
    left
    refine globalQuadratic_of_int_affine h2a U u0 (fun x => ?_)
    rcases hsplit x with h | h
    · exact h
    · exact absurd ⟨F x, h.symm⟩ (hVe x)
  obtain ⟨x₀, hx₀⟩ := hUe
  obtain ⟨y₀, hy₀⟩ := hVe
  let KU : AddSubgroup (Fin n → ℤ) :=
    { carrier := {h | 2 * a ∣ U ⬝ᵥ h}
      add_mem' := by
        intro x y hx hy; show 2 * a ∣ U ⬝ᵥ (x + y); rw [dotProduct_add]; exact dvd_add hx hy
      zero_mem' := by show 2 * a ∣ U ⬝ᵥ 0; rw [dotProduct_zero]; exact dvd_zero _
      neg_mem' := by
        intro x hx; show 2 * a ∣ U ⬝ᵥ (-x); rw [dotProduct_neg]; exact (dvd_neg).mpr hx }
  let KV : AddSubgroup (Fin n → ℤ) :=
    { carrier := {h | 2 * a ∣ V ⬝ᵥ h}
      add_mem' := by
        intro x y hx hy; show 2 * a ∣ V ⬝ᵥ (x + y); rw [dotProduct_add]; exact dvd_add hx hy
      zero_mem' := by show 2 * a ∣ V ⬝ᵥ 0; rw [dotProduct_zero]; exact dvd_zero _
      neg_mem' := by
        intro x hx; show 2 * a ∣ V ⬝ᵥ (-x); rw [dotProduct_neg]; exact (dvd_neg).mpr hx }
  have memU : ∀ g, g ∈ KU ↔ 2 * a ∣ U ⬝ᵥ (g + x₀) + u0 := by
    intro g
    rw [affine_dvd_iff_sub _ _ _ hx₀, add_sub_cancel_right]; exact Iff.rfl
  have memV : ∀ g, g - (y₀ - x₀) ∈ KV ↔ 2 * a ∣ V ⬝ᵥ (g + x₀) + v0 := by
    intro g
    rw [affine_dvd_iff_sub _ _ _ hy₀, show g + x₀ - y₀ = g - (y₀ - x₀) by abel]; exact Iff.rfl
  have res := addSubgroup_two_coset_cover KU KV (y₀ - x₀)
    (fun g => by rw [memU, memV]; exact hcover _)
    (fun g hg hg' => hboth _ ((memU g).mp hg) ((memV g).mp hg'))
  have hdoubleU : ∀ i, a ∣ U i := by
    intro i
    have h := res.2.2.2 (Pi.single i 1)
    change 2 * a ∣ U ⬝ᵥ (Pi.single i 1 + Pi.single i 1) at h
    rw [dotProduct_add, dotProduct_single, mul_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linarith⟩
  have hdoubleV : ∀ i, a ∣ V i := by
    intro i
    have h : Pi.single i 1 + Pi.single i 1 ∈ KV := res.1 ▸ res.2.2.2 (Pi.single i 1)
    change 2 * a ∣ V ⬝ᵥ (Pi.single i 1 + Pi.single i 1) at h
    rw [dotProduct_add, dotProduct_single, mul_one] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linarith⟩
  choose p hp using hdoubleU
  choose q hq using hdoubleV
  have hUp : ∀ x : Fin n → ℤ, U ⬝ᵥ x = a * (p ⬝ᵥ x) := by
    intro x; simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; rw [hp i]; ring
  have hVq : ∀ x : Fin n → ℤ, V ⬝ᵥ x = a * (q ⬝ᵥ x) := by
    intro x; simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; rw [hq i]; ring
  obtain ⟨c, hc⟩ : a ∣ u0 := by
    have h := dvd_trans (dvd_mul_left a 2) hx₀
    rw [hUp] at h
    exact (dvd_add_right (dvd_mul_right a _)).mp h
  obtain ⟨c', hc'⟩ : a ∣ v0 := by
    have h := dvd_trans (dvd_mul_left a 2) hy₀
    rw [hVq] at h
    exact (dvd_add_right (dvd_mul_right a _)).mp h
  have hUx : ∀ x, U ⬝ᵥ x + u0 = a * (p ⬝ᵥ x + c) := by intro x; rw [hUp, hc]; ring
  have hVx : ∀ x, V ⬝ᵥ x + v0 = a * (q ⬝ᵥ x + c') := by intro x; rw [hVq, hc']; ring
  have key2 : ∀ X : ℤ, (2 * a ∣ a * X ↔ (2 : ℤ) ∣ X) := by
    intro X; rw [mul_comm 2 a]; exact mul_dvd_mul_iff_left ha
  have evU : ∀ x, 2 * a ∣ U ⬝ᵥ x + u0 ↔ (2 : ℤ) ∣ p ⬝ᵥ x + c := fun x => by rw [hUx]; exact key2 _
  have evV : ∀ x, 2 * a ∣ V ⬝ᵥ x + v0 ↔ (2 : ℤ) ∣ q ⬝ᵥ x + c' := fun x => by rw [hVx]; exact key2 _
  have cov2 : ∀ x, (2 : ℤ) ∣ p ⬝ᵥ x + c ∨ (2 : ℤ) ∣ q ⬝ᵥ x + c' :=
    fun x => (hcover x).imp (evU x).mp (evV x).mp
  have dis2 : ∀ x, (2 : ℤ) ∣ p ⬝ᵥ x + c → ¬ (2 : ℤ) ∣ q ⬝ᵥ x + c' :=
    fun x h h' => hboth x ((evU x).mpr h) ((evV x).mpr h')
  have hcc : ¬ (2 : ℤ) ∣ c - c' := by
    have h1 := cov2 0; have h2 := dis2 0
    simp only [dotProduct_zero, zero_add] at h1 h2
    omega
  right
  refine ⟨p, q, c, c', fun i => ?_, ?_, hcc, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := cov2 (Pi.single i 1); have h2 := dis2 (Pi.single i 1)
    simp only [dotProduct_single, mul_one] at h1 h2
    omega
  · by_contra hall
    push_neg at hall
    have hev : ∀ x : Fin n → ℤ, (2 : ℤ) ∣ p ⬝ᵥ x :=
      fun x => Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hall i) _
    have h1 : (2 : ℤ) ∣ p ⬝ᵥ x₀ + c := (evU x₀).mp hx₀
    have h2 : (2 : ℤ) ∣ q ⬝ᵥ y₀ + c' := (evV y₀).mp hy₀
    have h3 := dis2 y₀
    have e1 := hev x₀; have e2 := hev y₀
    have h4 : (2 : ℤ) ∣ p ⬝ᵥ y₀ + c := by omega
    exact h3 h4 h2
  · have hh := hUdiv x ((evU x).mpr h)
    rw [hUx] at hh
    have : a * (2 * F x) = a * (p ⬝ᵥ x + c) := by linarith
    exact mul_left_cancel₀ ha this
  · have hvx : 2 * a ∣ V ⬝ᵥ x + v0 := (evV x).mpr ((cov2 x).resolve_left h)
    have hh := hVdiv x hvx
    rw [hVx] at hh
    have : a * (2 * F x) = a * (q ⬝ᵥ x + c') := by linarith
    exact mul_left_cancel₀ ha this

theorem parityFn_parityAffine : ParityAffineNF (scalarOut parityFn) := by
  refine ⟨fun _ => 1, fun _ => -3, 0, 1, fun _ => by norm_num, ⟨0, by norm_num⟩, by norm_num, fun x => ?_⟩
  have hx : x = fun _ => x 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have h1 : (fun _ : Fin 1 => (1 : ℤ)) ⬝ᵥ x = x 0 := by simp [dotProduct]
  have h2 : (fun _ : Fin 1 => (-3 : ℤ)) ⬝ᵥ x = -3 * x 0 := by simp [dotProduct]
  have hs : scalarOut parityFn x = parityFn (fun _ => x 0) 0 := by rw [scalarOut, ← hx]
  rw [h1, h2, hs, parityFn_apply]
  constructor
  · intro h; split_ifs with h' <;> omega
  · intro h; split_ifs with h' <;> omega

theorem plusMinus_not_relUnique : ¬ RelUnique (Rn (n := 1) 1 0 0 (-1) 0 0) := by
  intro h
  have h1 : Rn (n := 1) 1 0 0 (-1) 0 0 (fun _ => 1) 1 := by simp [Rn, Pn, dotProduct, Matrix.neg_mulVec, Matrix.one_mulVec]
  have h2 : Rn (n := 1) 1 0 0 (-1) 0 0 (fun _ => 1) (-1) := by simp [Rn, Pn, dotProduct, Matrix.neg_mulVec, Matrix.one_mulVec]
  have := h _ _ _ h1 h2
  norm_num at this

theorem sameParity_not_function :
    ¬ ∃ F : ℤ → ℤ, ∀ x y : ℤ, (2 * y - x) * (2 * y - x - 2) = 0 ↔ y = F x := by
  rintro ⟨F, hF⟩
  have h0 := (hF 0 0).mp (by norm_num)
  have h1 := (hF 0 1).mp (by norm_num)
  omega

theorem modThree_not_total : ¬ ∀ x : ℤ, ∃ y : ℤ, (3 * y - x) * (3 * y - x + 1) = 0 := by
  intro h
  obtain ⟨y, hy⟩ := h 2
  rcases mul_eq_zero.mp hy with h | h <;> omega

end DiophCompression.ResearchUpgrade
