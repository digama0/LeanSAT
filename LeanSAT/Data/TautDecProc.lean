/-
Copyright (c) the LeanSAT contributors.

Authors: Wojciech Nawrocki
-/

import Std

/-! Tautology decision procedure -/

/-- `encodes enc C` says that the hashmap `enc` encodes the (non-tautological) clause `C`.
More generally, `encodes enc C i` says that `enc` encodes the disjunction of all but the
first `i` literals of `C`. -/
def encodes (enc : HashMap Var Bool) (C : IClause) (start : Nat := 0) : Prop :=
  (∀ j : Fin C.size, start ≤ j → enc.find? C[j].var = .some C[j].polarity) ∧
    ∀ x : Var, enc.contains x ↔ ∃ j : Fin C.size, start ≤ j ∧ C[j].var = x

theorem encodes_empty (C : IClause) : encodes HashMap.empty C (Array.size C) := by
  simp [encodes]; intro j; exact not_le_of_lt j.isLt

theorem not_tautology_of_encodes (C : IClause) (enc : HashMap Var Bool) (h : encodes enc C) :
    ¬ (toPropFun C = ⊤) := by
  rw [tautology_iff]; simp only [not_exists, not_and]
  intros l₁ hl₁ l₂ hl₂ heq
  have ⟨i, hi⟩ := C.get_of_mem_data hl₁
  have ⟨j, hj⟩ := C.get_of_mem_data hl₂
  simp only [encodes, zero_le, forall_true_left, true_and] at h
  have hi' := h.1 i
  rw [hi, heq, ILit.toVar_negate, ILit.polarity_negate] at hi'
  have hj' := h.1 j
  rw [hj, hi'] at hj'
  simp at hj'

theorem encodes_insert_of_find?_eq_none {C : IClause} {i : Nat} {enc : HashMap Var Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h: HashMap.find? enc C[i].var = none) :
    encodes (HashMap.insert enc C[i].var C[i].polarity) C i := by
  constructor
  . intro j hile
    cases lt_or_eq_of_le hile
    case inl h' =>
      have := henc.1 _ (Nat.succ_le_of_lt h')
      rw [HashMap.find?_insert_of_ne, this]
      rw [bne_iff_ne, ne_eq]
      intro hc
      rw [←hc, h] at this; contradiction
    case inr h' =>
      cases h'
      simp [HashMap.find?_insert]
  . intro x
    rw [HashMap.contains_insert, henc.2 x, beq_iff_eq]; simp only [getElem_fin]
    constructor
    . rintro (⟨j, hile, rfl⟩ | rfl)
      . use j, (Nat.le_succ i).trans hile
      . use ⟨i, ilt⟩
    . rintro ⟨j, hile, rfl⟩
      cases lt_or_eq_of_le hile
      case inl h' =>
        left; use j, Nat.succ_le_of_lt h'
      case inr h' =>
        right; simp [h']

theorem tautology_of_encodes_of_find?_eq_some
      {C : IClause} {i : Nat} {enc : HashMap Var Bool} {p : Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h : HashMap.find? enc C[i].var = some p)
      (hpne : p ≠ C[i].polarity) :
    toPropFun C = ⊤ := by
  rw [tautology_iff]
  use C[i], C.get_mem_data ⟨i, ilt⟩
  have : enc.contains C[i].var := by
    rw [HashMap.contains_iff]; use p
  rw [henc.2] at this
  rcases this with ⟨j, hj, h'⟩
  use C[j], C.get_mem_data j
  ext; rw [ILit.toVar_negate, h']
  have := henc.1 j hj
  rw [h', h, Option.some.injEq] at this
  rw [ILit.polarity_negate, Bool.eq_bnot_to_not_eq, ←this]
  exact hpne.symm

theorem encode_of_encodes_of_find?_eq_some
      {C : IClause} {i : Nat} {enc : HashMap Var Bool} {p : Bool}
      (ilt: i < C.size)
      (henc : encodes enc C (i + 1))
      (h : HashMap.find? enc C[i].var = some p)
      (hpeq : p = C[i].polarity) :
    encodes enc C i := by
  constructor
  . intro j hile
    cases lt_or_eq_of_le hile
    case inl h' =>
      exact henc.1 _ (Nat.succ_le_of_lt h')
    case inr h' => cases h'; simp [h, hpeq]
  . intro x
    rw [henc.2]
    constructor
    . rintro ⟨j, hile, rfl⟩
      use j, (Nat.le_succ i).trans hile
    . rintro ⟨j, hile, rfl⟩
      cases lt_or_eq_of_le hile
      case inl h' => use j, Nat.succ_le_of_lt h'
      case inr h' =>
        have : enc.contains C[i].var := by
          rw [HashMap.contains_iff]; use p
        rw [henc.2] at this
        rcases this with ⟨j', hj', h''⟩
        use j', hj'
        rw [h'']; cases h'; simp

def checkTautoAux (C : IClause) : { b : Bool // b ↔ toPropFun C = ⊤ } :=
  go C.size (le_refl _) .empty C.encodes_empty
where
  go : (i : Nat) → i ≤ C.size → (acc : HashMap Var Bool) → encodes acc C i →
      { b : Bool // b ↔ toPropFun C = ⊤ }
    | 0,   _,  acc, hinv => ⟨false, by simp [C.not_tautology_of_encodes acc hinv]⟩
    | i+1, hi, acc, hinv =>
        have ilt := Nat.lt_of_succ_le hi
        match h: acc.find? C[i].var with
          | .none   => go i (le_of_lt ilt) _ (encodes_insert_of_find?_eq_none ilt hinv h)
          | .some p =>
              if hp: p = C[i].polarity then
                go i (le_of_lt ilt) _ (encode_of_encodes_of_find?_eq_some ilt hinv h hp)
              else
                ⟨true, by simp [tautology_of_encodes_of_find?_eq_some ilt hinv h hp]⟩

-- slow instance boo
-- instance : DecidablePred (IClause.toPropFun · = ⊤) :=
--   fun C => match checkTautoAux C with
--     | ⟨true, h⟩  => .isTrue (h.mp rfl)
--     | ⟨false, h⟩ => .isFalse fun hC => nomatch h.mpr hC

/-- Check whether a clause is a tautology. The type is a hack for early-return. The clause is
tautological iff `none` is returned. -/
@[deprecated checkTautoAux]
def checkTautoAux' (C : IClause) : Option (HashMap Var Bool) :=
  C.foldlM (init := .empty) fun acc l => do
    match acc.find? l.var with
    | .none => acc.insert l.var l.polarity
    | .some p => if p ≠ l.polarity then none else acc

/-! Partial assignments -/

/-- A partial assignment to propositional variables. -/
-- TODO: Using `HashMap` for this is cache-inefficient but I don't have time to verify better
-- structures rn
abbrev PartPropAssignment := HashMap Var Bool

namespace PartPropAssignment

/-- Interpret the assignment (x ↦ ⊤, y ↦ ⊥) as x ∧ ¬y, for example. -/
-- NOTE: Partial assignments really are more like formulas than they are like assignments because
-- there is no nice to way to extend one to a `PropAssignment` (i.e. a total assignment).
def toPropFun (τ : PartPropAssignment) : PropFun Var :=
  τ.fold (init := ⊤) fun acc x v => acc ⊓ if v then .var x else (.var x)ᶜ

instance : ToString PartPropAssignment where
  toString τ := String.intercalate " ∧ "
    (τ.fold (init := []) (f := fun acc x p => s!"{ILit.mk x p}" :: acc))

open PropFun

theorem satisfies_iff (τ : PartPropAssignment) (σ : PropAssignment Var) :
    σ ⊨ τ.toPropFun ↔ ∀ x p, τ.find? x = some p → σ x = p :=
  ⟨mp, mpr⟩
where
  mp := fun h => by
    intro x p? hFind
    have ⟨φ, hφ⟩ := τ.fold_of_mapsTo_of_comm
      (init := ⊤) (f := fun acc x v => acc ⊓ if v then PropFun.var x else (PropFun.var x)ᶜ)
      hFind ?comm
    case comm =>
      intros
      dsimp
      ac_rfl
    rw [toPropFun, hφ] at h
    aesop

  mpr := fun h => by
    apply HashMap.foldRecOn (hInit := satisfies_tr)
    intro φ x p hφ hFind
    rw [satisfies_conj]
    refine ⟨hφ, ?_⟩
    have := h _ _ hFind
    split <;> simp [*]

end PartPropAssignment

namespace IClause

/-- Reduces a clause by a partial assignment. Returns `none` if it became satisfied,
otherwise `some C'` where `C'` is the reduced clause. -/
def reduce (C : IClause) (τ : PartPropAssignment) : Option IClause :=
  C.foldlM (init := #[]) fun acc l =>
    match τ.find? l.var with
    | some v => if v = l.polarity then none else acc
    | none => some <| acc.push l

theorem reduce_characterization (C : IClause) (σ : PartPropAssignment) :
    SatisfiesM (fun C' =>
      ∀ l ∈ C.data, (!σ.contains l.var → l ∈ C'.data) ∧
        σ.find? l.var ≠ some l.polarity) (reduce C σ) := by
  have := C.SatisfiesM_foldlM (init := #[]) (f := fun acc l =>
      match σ.find? l.var with
      | some v => if v = l.polarity then none else acc
      | none => some <| acc.push l)
    (motive := fun sz acc =>
      ∀ (i : Fin C.size), i < sz → (!σ.contains C[i].var → C[i] ∈ acc.data) ∧
        σ.find? C[i].var ≠ some C[i].polarity)
    (h0 := by simp)
    (hf := by
      simp only [SatisfiesM_Option_eq, getElem_fin]
      intro sz acc ih acc'
      split; split
      . simp
      next p hFind hP =>
        intro h i hLt; injection h with h; rw [← h]
        refine Or.elim (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt)) (ih i) fun hEq => ?_
        simp only [hEq]
        refine ⟨?l, fun h => ?r⟩
        case r =>
          rw [hFind] at h
          injection h with h
          exact hP h
        case l =>
          have := HashMap.contains_iff _ _ |>.mpr ⟨_, hFind⟩
          simp_all
      next p hFind =>
        intro h i hLt; injection h with h; rw [← h]
        simp only [Array.push_data, List.mem_append, List.mem_singleton]
        refine Or.elim (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt)) (fun hLt => ?_) fun hEq => ?_
          <;> aesop
      )
  dsimp [reduce]
  apply SatisfiesM.imp this
  intro C' hRed
  exact fun l hL =>
    have ⟨i, h⟩ := Array.get_of_mem_data hL
    h ▸ hRed i i.isLt

open PropFun in
theorem reduce_eq_some (C C' : IClause) (σ : PartPropAssignment) :
    reduce C σ = some C' → C.toPropFun ⊓ σ.toPropFun ≤ C'.toPropFun := by
  intro hSome
  have hRed := SatisfiesM_Option_eq.mp (reduce_characterization C σ) _ hSome
  refine entails_ext.mpr fun τ hτ => ?_
  rw [satisfies_conj] at hτ
  have ⟨l, hL, hτL⟩ := IClause.satisfies_iff.mp hτ.left
  by_cases hCont : σ.contains l.var
  next =>
    exfalso
    have ⟨p, hFind⟩ := HashMap.contains_iff _ _ |>.mp hCont
    have := PartPropAssignment.satisfies_iff _ _ |>.mp hτ.right _ _ hFind
    have : p = l.polarity := by
      rw [ILit.satisfies_iff, this] at hτL
      assumption
    exact hRed l hL |>.right (this ▸ hFind)
  next =>
    simp only [Bool.not_eq_true, Bool.bnot_eq_to_not_eq] at *
    exact IClause.satisfies_iff.mpr ⟨l, (hRed l hL).left hCont, hτL⟩

/-- When `C` is not a tautology, return the smallest assignment falsifying it. When it is not,
return an undetermined assignment. -/
def toFalsifyingAssignment (C : IClause) : PartPropAssignment :=
  C.foldl (init := .empty) fun acc l => acc.insert l.var !l.polarity

theorem toFalsifyingAssignment_characterization (C : IClause) : C.toPropFun ≠ ⊤ →
    (∀ i : Fin C.size, C.toFalsifyingAssignment.find? C[i].var = some !C[i].polarity) ∧
    (∀ x p, C.toFalsifyingAssignment.find? x = some p → (ILit.mk x !p) ∈ C.data) := by
  intro hTauto
  have := C.foldl_induction
    (motive := fun (sz : Nat) (τ : PartPropAssignment) =>
      (∀ i : Fin C.size, i < sz → τ.find? C[i].var = some !C[i].polarity) ∧
      (∀ x p, τ.find? x = some p → (ILit.mk x !p) ∈ C.data))
    (init := .empty)
    (f := fun acc l => acc.insert l.var !l.polarity)
    (h0 := by simp)
    (hf := by
      intro sz τ ⟨ih₁, ih₂⟩
      refine ⟨?step₁, ?step₂⟩
      case step₁ =>
        intro i hLt
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hLt) with
        | inl h =>
          by_cases hEq : C[sz].var = C[i].var
          . have : C[sz].polarity = C[i].polarity := by
              by_contra hPol
              have : C[sz] = -C[i] := by
                apply ILit.ext <;> simp_all
              apply hTauto
              rw [tautology_iff]
              exact ⟨C[sz], Array.get_mem_data _ _, C[i], Array.get_mem_data _ _, this⟩
            have : C[sz] = C[i] := ILit.ext hEq this
            simp_all [HashMap.find?_insert]
          . simp only [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _ |>.mpr hEq), ih₁ i h]
        | inr h =>
          simp [h]
          rw [HashMap.find?_insert _ _ LawfulBEq.rfl]
      case step₂ =>
        intro x p hFind
        by_cases hEq : C[sz].var = x
        . rw [← hEq, HashMap.find?_insert _ _ (LawfulBEq.rfl)] at hFind
          injection hFind with hFind
          rw [← hEq, ← hFind]
          simp [Array.getElem_mem_data]
        . rw [HashMap.find?_insert_of_ne _ _ (bne_iff_ne _ _|>.mpr hEq)] at hFind
          apply ih₂ _ _ hFind)
  dsimp [toFalsifyingAssignment]
  exact ⟨fun i => this.left i i.isLt, this.right⟩

theorem toFalsifyingAssignment_ext (C : IClause) : C.toPropFun ≠ ⊤ →
    (∀ l, l ∈ C.data ↔ (toFalsifyingAssignment C).find? l.var = some !l.polarity) := by
  intro hTauto l
  have ⟨h₁, h₂⟩ := toFalsifyingAssignment_characterization C hTauto
  apply Iff.intro
  . intro hL
    have ⟨i, hI⟩ := Array.get_of_mem_data hL
    rw [← hI]
    exact h₁ i
  . intro hFind
    have := h₂ _ _ hFind
    rw [Bool.not_not, ILit.eta] at this
    exact this

theorem toPropFun_toFalsifyingAssignment (C : IClause) : C.toPropFun ≠ ⊤ →
    C.toFalsifyingAssignment.toPropFun = C.toPropFunᶜ := by
  intro hTauto
  have := toFalsifyingAssignment_ext C hTauto
  ext τ
  simp only [PartPropAssignment.satisfies_iff, PropFun.satisfies_neg, IClause.satisfies_iff,
    not_exists, not_and, ILit.satisfies_iff]
  apply Iff.intro
  . intro h l hL hτ
    have := h _ _ (this l |>.mp hL)
    simp [hτ] at this
  . intro h x p hFind
    have := this (ILit.mk x !p)
    simp only [ILit.var_mk, ILit.polarity_mk, Bool.not_not] at this
    have := h _ (this.mpr hFind)
    simp at this
    exact this

end IClause
