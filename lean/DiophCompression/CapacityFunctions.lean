/-
  DiophCompression/CapacityFunctions.lean — r05 必須E (session 5, 2026-08-27, claude.ai direct, no CC).
  Capacities as actual functions ℕ × ℕ → ℕ: the largest achievable arity, defined with `Nat.findGreatest`
  under the syntactic bound C(d+r+1, r+2) (weighted specialization capacity), which is what makes the
  greatest achievable arity a well-defined natural number. Together with the arity downward closure
  (ArityMonotonicity) the achievable arities form the INITIAL SEGMENT {n | n ≤ capacity} (`*_spec`, d ≥ 1;
  for d = 0 no arity is graph-achievable, since a constant polynomial represents ∅ or everything).
  Universality capacities: bound C(d+r+1, r+2) + 1 (U(n+1) ⇒ G(n) ⇒ n ≤ C); arity 0 is always
  universally achievable (∅ and the point are represented by the constants 1 and 0).
  Exported (GPT r04 §6 必須E names): graphCapacity{N,Z}_upper / _degree_one / _noWitness,
  plus the spec theorems and universalCapacity{N,Z} with spec/upper.
  s15 (2026-08-29, GPT r14 §9 / 必須F): the constructive chain lower bounds graphCapacity{N,Z}_chain_lower
  moved verbatim to CapacityChainLower.lean so that this module (and hence the Quadratic Witness Inertia
  closure) no longer imports TreeCoding. Names and statements unchanged.
-/
import DiophCompression.ArityMonotonicity
import DiophCompression.WeightedMPUP
import DiophCompression.BoundaryCasesZ

namespace DiophCompression

open MvPolynomial MPUP Classical

/-! ### Definitions -/

/-- Syntactic bound B(r,d) = C(d+r+1, r+2) on every graph-achievable arity. -/
def capBound (r d : ℕ) : ℕ := (d + r + 1).choose (r + 2)

noncomputable def graphCapacityN (r d : ℕ) : ℕ :=
  Nat.findGreatest (fun n => GraphAchievableN n r d) (capBound r d)

noncomputable def graphCapacityZ (r d : ℕ) : ℕ :=
  Nat.findGreatest (fun n => GraphAchievableZ n r d) (capBound r d)

noncomputable def universalCapacityN (r d : ℕ) : ℕ :=
  Nat.findGreatest (fun n => UniversalAchievableN n r d) (capBound r d + 1)

noncomputable def universalCapacityZ (r d : ℕ) : ℕ :=
  Nat.findGreatest (fun n => UniversalAchievableZ n r d) (capBound r d + 1)

/-! ### Graph capacity: initial-segment characterisation (d ≥ 1) -/

theorem graphCapacityN_upper (r d : ℕ) : graphCapacityN r d ≤ capBound r d :=
  Nat.findGreatest_le _

theorem graphCapacityZ_upper (r d : ℕ) : graphCapacityZ r d ≤ capBound r d :=
  Nat.findGreatest_le _

/-- Arity 0 is graph-achievable as soon as d ≥ 1 (from G(1, r, 1) by arity/degree monotonicity). -/
theorem graphAchievableN_zero (r d : ℕ) (hd : 1 ≤ d) : GraphAchievableN 0 r d :=
  graphAchievableN_mono_all (Nat.zero_le 1) le_rfl hd (graph_degree_one_achievable_N r)

theorem graphAchievableZ_zero (r d : ℕ) (hd : 1 ≤ d) : GraphAchievableZ 0 r d :=
  graph_arity_downward_Z (Nat.zero_le 1) (graphAchievableZ_mono le_rfl hd (graph_degree_one_achievable_Z r))

theorem graphCapacityN_spec (r d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    GraphAchievableN n r d ↔ n ≤ graphCapacityN r d := by
  constructor
  · intro h
    exact Nat.le_findGreatest (graph_dimension_le_totalDegreeCapacity_N h) h
  · intro hn
    have hcap : GraphAchievableN (graphCapacityN r d) r d := by
      unfold graphCapacityN
      exact Nat.findGreatest_spec (P := fun n => GraphAchievableN n r d) (n := capBound r d)
        (Nat.zero_le _) (graphAchievableN_zero r d hd)
    exact graph_arity_downward_N hn hcap

theorem graphCapacityZ_spec (r d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    GraphAchievableZ n r d ↔ n ≤ graphCapacityZ r d := by
  constructor
  · intro h
    exact Nat.le_findGreatest (graph_dimension_le_totalDegreeCapacity_Z h) h
  · intro hn
    have hcap : GraphAchievableZ (graphCapacityZ r d) r d := by
      unfold graphCapacityZ
      exact Nat.findGreatest_spec (P := fun n => GraphAchievableZ n r d) (n := capBound r d)
        (Nat.zero_le _) (graphAchievableZ_zero r d hd)
    exact graph_arity_downward_Z hn hcap

/-! ### Boundary values and the chain lower bound, in capacity form -/

theorem graphCapacityN_degree_one (r : ℕ) : graphCapacityN r 1 = 1 :=
  le_antisymm
    (graph_degree_one_le_one_N ((graphCapacityN_spec r 1 le_rfl _).mpr le_rfl))
    ((graphCapacityN_spec r 1 le_rfl 1).mp (graph_degree_one_achievable_N r))

theorem graphCapacityZ_degree_one (r : ℕ) : graphCapacityZ r 1 = 1 :=
  le_antisymm
    (graph_degree_one_le_one_Z ((graphCapacityZ_spec r 1 le_rfl _).mpr le_rfl))
    ((graphCapacityZ_spec r 1 le_rfl 1).mp (graph_degree_one_achievable_Z r))

theorem graphCapacityN_noWitness (d : ℕ) (hd : 1 ≤ d) : graphCapacityN 0 d = d :=
  le_antisymm
    (graph_no_witness_le ((graphCapacityN_spec 0 d hd _).mpr le_rfl))
    ((graphCapacityN_spec 0 d hd d).mp (graph_no_witness_achievable d hd))

theorem graphCapacityZ_noWitness (d : ℕ) (hd : 1 ≤ d) : graphCapacityZ 0 d = d :=
  le_antisymm
    (graph_no_witness_le_Z ((graphCapacityZ_spec 0 d hd _).mpr le_rfl))
    ((graphCapacityZ_spec 0 d hd d).mp (graph_no_witness_achievable_Z d hd))

/-! ### Universality capacity -/

/-- Arity 0 is universally achievable: the two subsets of the point are represented by constants. -/
theorem universalAchievableN_zero (r d : ℕ) : UniversalAchievableN 0 r d := by
  intro A _
  by_cases hA : (fun _ : Fin 0 => 0) ∈ A
  · refine ⟨0, Nat.zero_le _, C 0, by simp, ?_⟩
    intro a
    have ha : a = fun _ => 0 := funext fun i => i.elim0
    rw [ha]
    simp [evalAt, hA]
  · refine ⟨0, Nat.zero_le _, C 1, by simp, ?_⟩
    intro a
    have ha : a = fun _ => 0 := funext fun i => i.elim0
    rw [ha]
    simp [evalAt, hA]

theorem universalAchievableZ_zero (r d : ℕ) : UniversalAchievableZ 0 r d := by
  intro A _
  by_cases hA : (fun _ : Fin 0 => 0) ∈ A
  · refine ⟨0, Nat.zero_le _, C 0, by simp, ?_⟩
    intro a
    have ha : a = fun _ => 0 := funext fun i => i.elim0
    rw [ha]
    simp [evalAt, hA]
  · refine ⟨0, Nat.zero_le _, C 1, by simp, ?_⟩
    intro a
    have ha : a = fun _ => 0 := funext fun i => i.elim0
    rw [ha]
    simp [evalAt, hA]

theorem universalAchievableN_le {n r d : ℕ} (h : UniversalAchievableN n r d) : n ≤ capBound r d + 1 := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have := graph_dimension_le_totalDegreeCapacity_N (universal_implies_graph h)
    unfold capBound; omega

theorem universalAchievableZ_le {n r d : ℕ} (h : UniversalAchievableZ n r d) : n ≤ capBound r d + 1 := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have := graph_dimension_le_totalDegreeCapacity_Z (universal_implies_graph_Z h)
    unfold capBound; omega

theorem universalCapacityN_spec (r d n : ℕ) :
    UniversalAchievableN n r d ↔ n ≤ universalCapacityN r d := by
  constructor
  · intro h
    exact Nat.le_findGreatest (universalAchievableN_le h) h
  · intro hn
    have hcap : UniversalAchievableN (universalCapacityN r d) r d := by
      unfold universalCapacityN
      exact Nat.findGreatest_spec (P := fun n => UniversalAchievableN n r d) (n := capBound r d + 1)
        (Nat.zero_le _) (universalAchievableN_zero r d)
    exact universal_arity_downward_N hn hcap

theorem universalCapacityZ_spec (r d n : ℕ) :
    UniversalAchievableZ n r d ↔ n ≤ universalCapacityZ r d := by
  constructor
  · intro h
    exact Nat.le_findGreatest (universalAchievableZ_le h) h
  · intro hn
    have hcap : UniversalAchievableZ (universalCapacityZ r d) r d := by
      unfold universalCapacityZ
      exact Nat.findGreatest_spec (P := fun n => UniversalAchievableZ n r d) (n := capBound r d + 1)
        (Nat.zero_le _) (universalAchievableZ_zero r d)
    exact universal_arity_downward_Z hn hcap

theorem universalCapacityN_upper (r d : ℕ) : universalCapacityN r d ≤ capBound r d + 1 :=
  Nat.findGreatest_le _

theorem universalCapacityZ_upper (r d : ℕ) : universalCapacityZ r d ≤ capBound r d + 1 :=
  Nat.findGreatest_le _

/-- U ≤ G + 1 in capacity form (sandwich, ℕ). -/
theorem universalCapacityN_le_graphCapacityN_succ (r d : ℕ) (hd : 1 ≤ d) :
    universalCapacityN r d ≤ graphCapacityN r d + 1 := by
  have h := (universalCapacityN_spec r d _).mpr (le_refl (universalCapacityN r d))
  cases hu : universalCapacityN r d with
  | zero => exact Nat.zero_le _
  | succ m =>
    rw [hu] at h
    have := (graphCapacityN_spec r d hd m).mp (universal_implies_graph h)
    omega

end DiophCompression

#print axioms DiophCompression.graphCapacityN_spec
#print axioms DiophCompression.graphCapacityZ_spec
#print axioms DiophCompression.graphCapacityN_upper
#print axioms DiophCompression.graphCapacityZ_upper
#print axioms DiophCompression.graphCapacityN_degree_one
#print axioms DiophCompression.graphCapacityZ_degree_one
#print axioms DiophCompression.graphCapacityN_noWitness
#print axioms DiophCompression.graphCapacityZ_noWitness
#print axioms DiophCompression.universalCapacityN_spec
#print axioms DiophCompression.universalCapacityZ_spec
#print axioms DiophCompression.universalCapacityN_le_graphCapacityN_succ
