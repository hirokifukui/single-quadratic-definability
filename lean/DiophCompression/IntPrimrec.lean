/-
  DiophCompression/IntPrimrec.lean — APAL Structural Theory Gate 1 (session 24, 2026-08-31, claude.ai direct, 0 CC).
  mathlib at the release pin d46bd45 (the pin this file is built and audited against; see lakefile.lean) has no
  `Primrec` for ℤ arithmetic (ℤ is Primcodable only via `Primcodable.ofDenumerable`).
  This file supplies `Primrec₂ (· + ·)`, `Primrec₂ (· * ·)` on ℤ through the coding ℤ ≃ ℕ ⊕ ℕ
  (`Equiv.intEquivNatSumNat`), and derives computability of integer polynomial evaluation.
  Pure computability infrastructure — no Champagne mathematics; upstreamable.
-/
import Mathlib.Computability.Partrec
import Mathlib.Logic.Equiv.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

namespace DiophCompression

open Primrec

/-! ### The ℕ ⊕ ℕ coding of ℤ -/

/-- `inl a ↦ a`, `inr b ↦ -(b+1)`. -/
def intOfS : ℕ ⊕ ℕ → ℤ := Sum.elim Int.ofNat Int.negSucc

/-- The inverse of `Equiv.natSumNatEquivNat`: `2a ↦ inl a`, `2b+1 ↦ inr b`. -/
def natToS (n : ℕ) : ℕ ⊕ ℕ := if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)

theorem natSumNatEquivNat_natToS (n : ℕ) : Equiv.natSumNatEquivNat (natToS n) = n := by
  rw [Equiv.natSumNatEquivNat_apply]
  unfold natToS
  split_ifs with h <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega

theorem natSumNatEquivNat_symm_eq (n : ℕ) : Equiv.natSumNatEquivNat.symm n = natToS n := by
  conv_lhs => rw [← natSumNatEquivNat_natToS n]
  exact Equiv.symm_apply_apply _ _

theorem intEquivNatSumNat_symm_eq (s : ℕ ⊕ ℕ) : Equiv.intEquivNatSumNat.symm s = intOfS s := rfl

theorem encode_int_eq (z : ℤ) : Encodable.encode z = Equiv.intEquivNat z := rfl

theorem ofNat_int_eq (n : ℕ) : Denumerable.ofNat ℤ n = intOfS (natToS n) := by
  have h1 : Denumerable.ofNat ℤ n = Equiv.intEquivNat.symm n := Denumerable.ofNat_of_decode rfl
  rw [h1, Equiv.intEquivNat, Equiv.symm_trans_apply, natSumNatEquivNat_symm_eq, intEquivNatSumNat_symm_eq]

theorem encode_intOfS (s : ℕ ⊕ ℕ) : Encodable.encode (intOfS s) = Equiv.natSumNatEquivNat s := by
  rw [encode_int_eq, ← intEquivNatSumNat_symm_eq, Equiv.intEquivNat, Equiv.trans_apply,
    Equiv.apply_symm_apply]

theorem primrec_natToS : Primrec natToS :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (Primrec.sumInl.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
    (Primrec.sumInr.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))

theorem primrec_intOfS : Primrec intOfS := by
  apply Primrec.encode_iff.mp
  refine (Primrec.sumCasesOn (f := fun s : ℕ ⊕ ℕ => s) (g := fun _ a => 2 * a)
    (h := fun _ b => 2 * b + 1) Primrec.id
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 1)).to₂).of_eq
    fun s => ?_
  rw [encode_intOfS, Equiv.natSumNatEquivNat_apply]
  cases s <;> rfl

/-! ### Addition and multiplication on the coding -/

def intAddS : ℕ ⊕ ℕ → ℕ ⊕ ℕ → ℕ ⊕ ℕ
  | Sum.inl a, Sum.inl b => Sum.inl (a + b)
  | Sum.inl a, Sum.inr b => if b < a then Sum.inl (a - b - 1) else Sum.inr (b - a)
  | Sum.inr a, Sum.inl b => if a < b then Sum.inl (b - a - 1) else Sum.inr (a - b)
  | Sum.inr a, Sum.inr b => Sum.inr (a + b + 1)

def intMulS : ℕ ⊕ ℕ → ℕ ⊕ ℕ → ℕ ⊕ ℕ
  | Sum.inl a, Sum.inl b => Sum.inl (a * b)
  | Sum.inl a, Sum.inr b => if a = 0 then Sum.inl 0 else Sum.inr (a * (b + 1) - 1)
  | Sum.inr a, Sum.inl b => if b = 0 then Sum.inl 0 else Sum.inr ((a + 1) * b - 1)
  | Sum.inr a, Sum.inr b => Sum.inl ((a + 1) * (b + 1))

theorem intOfS_add (s t : ℕ ⊕ ℕ) : intOfS s + intOfS t = intOfS (intAddS s t) := by
  rcases s with a | a <;> rcases t with b | b <;> simp only [intOfS, intAddS, Sum.elim_inl, Sum.elim_inr] <;>
    (try split_ifs) <;> simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, Sum.elim_inl, Sum.elim_inr] <;>
    omega

theorem intOfS_mul (s t : ℕ ⊕ ℕ) : intOfS s * intOfS t = intOfS (intMulS s t) := by
  rcases s with a | a <;> rcases t with b | b
  · simp [intOfS, intMulS]
  · simp only [intOfS, intMulS, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h
    · subst h; simp
    · have h1 : 1 ≤ a * (b + 1) := Nat.mul_pos (Nat.pos_of_ne_zero h) (Nat.succ_pos b)
      simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, Sum.elim_inr]
      rw [Nat.cast_sub h1]
      push_cast
      ring
  · simp only [intOfS, intMulS, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h
    · subst h; simp
    · have h1 : 1 ≤ (a + 1) * b := Nat.mul_pos (Nat.succ_pos a) (Nat.pos_of_ne_zero h)
      simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, Sum.elim_inr]
      rw [Nat.cast_sub h1]
      push_cast
      ring
  · simp only [intOfS, intMulS, Sum.elim_inl, Sum.elim_inr, Int.negSucc_eq, Int.ofNat_eq_natCast]
    push_cast
    ring

theorem primrec₂_intAddS : Primrec₂ intAddS := by
  have hL : Primrec fun p : ℕ × (ℕ ⊕ ℕ) => intAddS (Sum.inl p.1) p.2 := by
    have h := Primrec.sumCasesOn (f := fun p : ℕ × (ℕ ⊕ ℕ) => p.2)
        (g := fun p b => (Sum.inl (p.1 + b) : ℕ ⊕ ℕ))
        (h := fun p b => if b < p.1 then Sum.inl (p.1 - b - 1) else Sum.inr (b - p.1)) Primrec.snd
        (Primrec.sumInl.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
        (Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
          (Primrec.sumInl.comp (Primrec.nat_sub.comp
            (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 1)))
          (Primrec.sumInr.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.fst.comp Primrec.fst)))).to₂
    refine h.of_eq ?_
    rintro ⟨a, b | b⟩ <;> rfl
  have hR : Primrec fun p : ℕ × (ℕ ⊕ ℕ) => intAddS (Sum.inr p.1) p.2 := by
    have h := Primrec.sumCasesOn (f := fun p : ℕ × (ℕ ⊕ ℕ) => p.2)
        (g := fun p b => if p.1 < b then Sum.inl (b - p.1 - 1) else Sum.inr (p.1 - b))
        (h := fun p b => (Sum.inr (p.1 + b + 1) : ℕ ⊕ ℕ)) Primrec.snd
        (Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
          (Primrec.sumInl.comp (Primrec.nat_sub.comp
            (Primrec.nat_sub.comp Primrec.snd (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)))
          (Primrec.sumInr.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂
        (Primrec.sumInr.comp (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 1))).to₂
    refine h.of_eq ?_
    rintro ⟨a, b | b⟩ <;> rfl
  have h := Primrec.sumCasesOn (f := fun p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) => p.1)
      (g := fun p a => intAddS (Sum.inl a) p.2) (h := fun p a => intAddS (Sum.inr a) p.2) Primrec.fst
      (hL.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
      (hR.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
  refine h.of_eq ?_
  rintro ⟨a | a, t⟩ <;> rfl

theorem primrec₂_intMulS : Primrec₂ intMulS := by
  have hL : Primrec fun p : ℕ × (ℕ ⊕ ℕ) => intMulS (Sum.inl p.1) p.2 := by
    have h := Primrec.sumCasesOn (f := fun p : ℕ × (ℕ ⊕ ℕ) => p.2)
        (g := fun p b => (Sum.inl (p.1 * b) : ℕ ⊕ ℕ))
        (h := fun p b => if p.1 = 0 then Sum.inl 0 else Sum.inr (p.1 * (b + 1) - 1)) Primrec.snd
        (Primrec.sumInl.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
          (Primrec.const (Sum.inl 0))
          (Primrec.sumInr.comp (Primrec.nat_sub.comp
            (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
              (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))) (Primrec.const 1)))).to₂
    refine h.of_eq ?_
    rintro ⟨a, b | b⟩ <;> rfl
  have hR : Primrec fun p : ℕ × (ℕ ⊕ ℕ) => intMulS (Sum.inr p.1) p.2 := by
    have h := Primrec.sumCasesOn (f := fun p : ℕ × (ℕ ⊕ ℕ) => p.2)
        (g := fun p b => if b = 0 then Sum.inl 0 else Sum.inr ((p.1 + 1) * b - 1))
        (h := fun p b => (Sum.inl ((p.1 + 1) * (b + 1)) : ℕ ⊕ ℕ)) Primrec.snd
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
          (Primrec.const (Sum.inl 0))
          (Primrec.sumInr.comp (Primrec.nat_sub.comp
            (Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
              Primrec.snd) (Primrec.const 1)))).to₂
        (Primrec.sumInl.comp (Primrec.nat_mul.comp
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
          (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))).to₂
    refine h.of_eq ?_
    rintro ⟨a, b | b⟩ <;> rfl
  have h := Primrec.sumCasesOn (f := fun p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) => p.1)
      (g := fun p a => intMulS (Sum.inl a) p.2) (h := fun p a => intMulS (Sum.inr a) p.2) Primrec.fst
      (hL.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
      (hR.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
  refine h.of_eq ?_
  rintro ⟨a | a, t⟩ <;> rfl

/-! ### ℤ arithmetic is primitive recursive -/

theorem primrec₂_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff]
  have h : Primrec fun p : ℕ × ℕ => intOfS (intAddS (natToS p.1) (natToS p.2)) :=
    primrec_intOfS.comp (primrec₂_intAddS.comp (primrec_natToS.comp Primrec.fst)
      (primrec_natToS.comp Primrec.snd))
  refine h.of_eq ?_
  rintro ⟨m, n⟩
  simp only [ofNat_int_eq, intOfS_add]

theorem primrec₂_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff]
  have h : Primrec fun p : ℕ × ℕ => intOfS (intMulS (natToS p.1) (natToS p.2)) :=
    primrec_intOfS.comp (primrec₂_intMulS.comp (primrec_natToS.comp Primrec.fst)
      (primrec_natToS.comp Primrec.snd))
  refine h.of_eq ?_
  rintro ⟨m, n⟩
  simp only [ofNat_int_eq, intOfS_mul]

theorem computable₂_int_add : Computable₂ ((· + ·) : ℤ → ℤ → ℤ) := primrec₂_int_add.to_comp
theorem computable₂_int_mul : Computable₂ ((· * ·) : ℤ → ℤ → ℤ) := primrec₂_int_mul.to_comp

/-! ### Integer polynomial evaluation is computable -/

open MvPolynomial

/-- For any index type `σ`, if every coordinate `a ↦ x a i` is primitive recursive then so is `a ↦ p(x a)`. -/
theorem primrec_eval_of_coords {σ α : Type*} [Primcodable α] (p : MvPolynomial σ ℤ)
    (x : α → σ → ℤ) (hx : ∀ i, Primrec fun a => x a i) :
    Primrec fun a => eval (x a) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine (Primrec.const c).of_eq fun a => ?_
    simp
  | add p q hp hq =>
    refine (primrec₂_int_add.comp hp hq).of_eq fun a => ?_
    simp
  | mul_X p i hp =>
    refine (primrec₂_int_mul.comp hp (hx i)).of_eq fun a => ?_
    simp

/-- For any index type `σ`, if every coordinate `a ↦ x a i` is computable then so is `a ↦ p(x a)`. -/
theorem computable_eval_of_coords {σ α : Type*} [Primcodable α] (p : MvPolynomial σ ℤ)
    (x : α → σ → ℤ) (hx : ∀ i, Computable fun a => x a i) :
    Computable fun a => eval (x a) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine (Computable.const c).of_eq fun a => ?_
    simp
  | add p q hp hq =>
    refine (computable₂_int_add.comp hp hq).of_eq fun a => ?_
    simp
  | mul_X p i hp =>
    refine (computable₂_int_mul.comp hp (hx i)).of_eq fun a => ?_
    simp

/-- Integer powers are primitive recursive. -/
theorem primrec_int_pow (d : ℕ) : Primrec fun z : ℤ => z ^ d := by
  induction d with
  | zero => exact (Primrec.const 1).of_eq fun z => by simp
  | succ d ih => exact (primrec₂_int_mul.comp ih Primrec.id).of_eq fun z => by rw [pow_succ]; rfl

theorem computable_eval_mvPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    Computable fun x : Fin n → ℤ => eval x p :=
  computable_eval_of_coords p (fun x => x) fun i => Computable.fin_app.comp Computable.id (Computable.const i)

end DiophCompression

#print axioms DiophCompression.primrec₂_int_add
#print axioms DiophCompression.primrec₂_int_mul
#print axioms DiophCompression.primrec_eval_of_coords
#print axioms DiophCompression.computable_eval_of_coords
#print axioms DiophCompression.primrec_int_pow
#print axioms DiophCompression.computable_eval_mvPolynomial
