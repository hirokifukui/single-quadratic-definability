/-
  DiophCompression/GraphToUniversalityN.lean — r05 必須C (session 5, 2026-08-26, claude.ai direct, no CC).
  Graph coding → universality, ℕ-unknowns, at ONE arity n, with exact resource accounting:
    UniversalPairN ν₀ δ₀ ∧ GraphAchievableN n r d ⟹ UniversalAchievableN n (r + ν₀ + 1) (2·max d δ₀).
  Mechanism (GPT r04 §6 必須C, = the local-arity extraction of the frozen `MPUP.Task1.multiUniversal_of_coder`,
  whose proof uses the coder at the single arity n only): for A ⊆ ℕ^n Diophantine, B := e(A) ⊆ ℕ is
  Diophantine (graph e ∧ A, then project the parameter block); the universal pair gives U representing B
  with ≤ ν₀ unknowns, degree ≤ δ₀; then a ∈ A ⟺ ∃ c, (c = e(a) ∧ c ∈ B), realised as the sum of squares
  of the graph polynomial and U with the output variable c turned into an unknown (`projectLast`).
  Witnesses: r' + ν'' + 1 ≤ r + ν₀ + 1 (c is the +1). Degree: 2·max(d, δ₀) from the two squares.
  Injectivity of e is used in the ⇐ direction (c = e a' with a' ∈ A forces a' = a); totality and
  soundness of the graph in the ⇒ direction. No dependence on `TupleCoderN` (all arities).
  Statements frozen 2026-08-26 (frozen statement file `GraphToUniversalityN_STATEMENTS.lean`); proof body = the
  frozen Task1 proof with `hC n` replaced by `hG` (Task1.lean lines 458–516, untouched there).
-/
import MPUP.Task1
import DiophCompression.Sandwich

namespace DiophCompression

open MvPolynomial MPUP

/-- Main theorem (GPT r04 必須C): graph coding at arity n plus a one-parameter universal pair
    gives universality at arity n with overhead (ν₀ + 1 witnesses, degree doubling). -/
theorem graph_to_universality_N {n r d ν₀ δ₀ : ℕ}
    (hU : UniversalPairN ν₀ δ₀) (hG : GraphAchievableN n r d) :
    UniversalAchievableN n (r + ν₀ + 1) (2 * max d δ₀) := by
  intro A hA
  obtain ⟨e, he, r', hr', C, hCd, hCrep⟩ := hG
  obtain ⟨rA, PA, hPArep⟩ := hA
  have hA'rep : RepresentsN (weakenParams 1 PA)
      {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} :=
    representsN_weakenParams PA A hPArep
  have hSrep := representsN_conj C (weakenParams 1 PA) (graph e)
    {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} hCrep hA'rep
  have hSdioph : DiophN (graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}) :=
    ⟨_, _, hSrep⟩
  have hBdioph := diophN_projectBlock _ hSdioph
  obtain ⟨ν'', hν'', PB, hPBd, hPBrep⟩ := hU _ hBdioph
  let g : Fin 1 → Fin (n+1) := fun _ => Fin.last n
  have hPB'rep := aux_representsN_renameParams g PB _ hPBrep
  have hConjrep := representsN_conj C (rename (Sum.map g id) PB) (graph e)
    {V : Fin (n+1) → ℕ | (fun i => V (g i)) ∈
      {c : Fin 1 → ℕ | ∃ a : Fin n → ℕ, Fin.append a c ∈
        graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}}}
    hCrep hPB'rep
  have hDrep := representsN_projectLast (conj C (rename (Sum.map g id) PB)) _ hConjrep
  have initA : ∀ (w : Fin n → ℕ) (x : ℕ),
      (fun i => (Fin.snoc w x : Fin (n+1) → ℕ) (Fin.castAdd 1 i)) = w := by
    intro w x; funext i; exact Fin.snoc_castSucc (α := fun _ => ℕ) x w i
  have hset : {a : Fin n → ℕ | ∃ cc, Fin.snoc a cc ∈
      (graph e ∩ {V : Fin (n+1) → ℕ | (fun i => V (g i)) ∈
        {c : Fin 1 → ℕ | ∃ a : Fin n → ℕ, Fin.append a c ∈
          graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}}})} = A := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨cc, hg, hb⟩
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc] at hg
      simp only [g, Fin.snoc_last] at hb
      obtain ⟨a', hab⟩ := hb
      rw [Fin.append_right_eq_snoc] at hab
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc] at hab
      obtain ⟨hc', haA⟩ := hab
      rw [initA a' cc] at haA
      have : a = a' := he (by rw [← hg, ← hc'])
      rw [this]; exact haA
    · intro ha
      refine ⟨e a, ?_, ?_⟩
      · simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
      · simp only [g, Fin.snoc_last]
        refine ⟨a, ?_⟩
        rw [Fin.append_right_eq_snoc]
        refine ⟨?_, ?_⟩
        · simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
        · rw [initA a (e a)]; exact ha
  rw [hset] at hDrep
  refine ⟨r' + ν'' + 1, ?_, projectLast (conj C (rename (Sum.map g id) PB)), ?_, hDrep⟩
  · show r' + ν'' + 1 ≤ r + ν₀ + 1; omega
  · refine (totalDegree_projectLast_le _).trans ?_
    refine (totalDegree_conj_le _ _).trans ?_
    have h1 : C.totalDegree ≤ d := hCd
    have h2 : (rename (Sum.map g id) PB).totalDegree ≤ δ₀ := (totalDegree_rename_le _ _).trans hPBd
    exact Nat.mul_le_mul (le_refl 2) (max_le_max h1 h2)

/-- The resource-distorted equivalence U ⟺ G at fixed arity (ℕ-unknowns), assuming a universal pair:
    U(n+1, r, d) ⟹ G(n, r, d) (Sandwich) and G(n, r, d) ⟹ U(n, r+ν₀+1, 2·max d δ₀). -/
theorem graph_universality_equivalence_N {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀) (n r d : ℕ) :
    (UniversalAchievableN (n + 1) r d → GraphAchievableN n r d) ∧
    (GraphAchievableN n r d → UniversalAchievableN n (r + ν₀ + 1) (2 * max d δ₀)) :=
  ⟨universal_implies_graph, graph_to_universality_N hU⟩

end DiophCompression

#print axioms DiophCompression.graph_to_universality_N
#print axioms DiophCompression.graph_universality_equivalence_N
