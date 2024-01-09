/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Jeremy Avigad
-/

import LeanSAT.Upstream.ToMathlib
import LeanSAT.Model.PropFun
import LeanSAT.Model.PropVars

namespace LeanSAT

open Model

/-! ### Literals -/

/-- The type `L` is a representation of literals over variables of type `ν`. -/
@[specialize]
class LitVar (L : Type u) (ν : outParam $ Type v) where
  negate : L → L
  mkPos : ν → L
  mkNeg : ν → L := fun x => negate (mkPos x)
  toVar : L → ν
  /-- true if positive -/
  polarity : L → Bool
  -- TODO: ν moreover needs to biject with PNat (perhaps in a separate typeclass)
  -- so that we can use variable names as array indices

namespace LitVar

def mkLit (L : Type u) {ν : Type v} [LitVar L ν] (x : ν) (p : Bool) : L :=
  if p then mkPos x else mkNeg x

variable {L : Type u} {ν : Type v} [LitVar L ν]

-- controversial maybe?
instance : Coe ν L :=
  ⟨mkPos⟩

-- Cayden TODO: Should this be InvolutiveNeg?
instance : Neg L :=
  ⟨negate⟩

@[simp] theorem negate_eq (l : L) : negate l = -l := rfl

instance [ToString ν] : ToString L where
  toString l := if polarity l then s!"{toVar l}" else s!"-{toVar l}"

def toPropForm (l : L) : PropForm ν :=
  if polarity l then .var (toVar l) else .neg (.var $ toVar l)

def toPropFun (l : L) : PropFun ν :=
  if polarity l then .var (toVar l) else (.var $ toVar l)ᶜ

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun l ↔ τ (toVar l) = polarity l := by
  dsimp [toPropFun, polarity]
  aesop

end LitVar

/-! ### Lawful literals -/

-- TODO: see if a shorter list of axioms implies this one
open LitVar in
class LawfulLitVar (L : Type u) (ν : Type v) [LitVar L ν] where
  toVar_negate (l : L) : toVar (-l) = toVar l
  toVar_mkPos (x : ν) : toVar (mkPos (L := L) x) = x
  toVar_mkNeg (x : ν) : toVar (mkNeg (L := L) x) = x
  polarity_negate (l : L) : polarity (-l) = !polarity l
  polarity_mkPos (x : ν) : polarity (mkPos (L := L) x) = true
  polarity_mkNeg (x : ν) : polarity (mkNeg (L := L) x) = false
  protected ext (l₁ l₂ : L) : toVar l₁ = toVar l₂ → polarity l₁ = polarity l₂ → l₁ = l₂

namespace LitVar
variable {L : Type u} {ν : Type v} [LitVar L ν] [LawfulLitVar L ν]
open LawfulLitVar

export LawfulLitVar (toVar_negate toVar_mkPos toVar_mkNeg polarity_negate polarity_mkPos polarity_mkNeg ext)

attribute [simp] toVar_negate toVar_mkPos toVar_mkNeg polarity_negate polarity_mkPos polarity_mkNeg
attribute [ext] LawfulLitVar.ext

@[simp] theorem var_mkLit (x : ν) (p : Bool) : toVar (mkLit L x p) = x := by
  dsimp [mkLit]; split <;> simp
@[simp] theorem polarity_mkLit (x : ν) (p : Bool) : polarity (mkLit L x p) = p := by
  dsimp [mkLit]; split <;> simp_all

@[simp] theorem eta (l : L) : mkLit L (toVar l) (polarity l) = l := by
  ext <;> simp
@[simp] theorem eta_neg (l : L) : mkLit L (toVar l) (!polarity l) = -l := by
  ext <;> simp

theorem mkPos_or_mkNeg (l : L) : l = mkPos (toVar l) ∨ l = mkNeg (toVar l) := by
  rw [← eta l]
  cases polarity l
  . apply Or.inr
    simp [mkLit]
  . apply Or.inl
    simp [mkLit]

@[simp] theorem negate_mkPos (v : ν) : -((mkPos v) : L) = mkNeg v := by
  ext
  · simp only [toVar_negate, toVar_mkNeg, toVar_mkPos]
  · simp only [polarity_negate, polarity_mkPos, Bool.not_true, polarity_mkNeg]

@[simp] theorem negate_mkNeg (v : ν) : -((mkNeg v) : L) = mkPos v := by
  ext
  · simp only [toVar_negate, toVar_mkNeg, toVar_mkPos]
  · simp only [polarity_negate, polarity_mkNeg, Bool.not_false, polarity_mkPos]

@[simp] theorem negate_negate (l : L) : negate (negate l) = l := by
  ext <;> simp only [negate_eq, toVar_negate, polarity_negate, Bool.not_not]

-- Cayden Q: Can we get this for free from InvolutiveNeg? Should we add an instance : ?
@[simp] theorem neg_neg (l : L) : -(-l) = l := by
  rw [← negate_eq, ← negate_eq]; exact negate_negate l

theorem ne_of_var_ne {l₁ l₂ : L} : (toVar l₁) ≠ (toVar l₂) → l₁ ≠ l₂ := by
  intro hne
  rw [ne_eq]
  rintro rfl
  contradiction

theorem ne_of_polarity_ne {l₁ l₂ : L} : polarity l₁ ≠ polarity l₂ → l₁ ≠ l₂ := by
  intro hne
  rw [ne_eq]
  rintro rfl
  contradiction

@[simp] theorem ne_neg_self (l : L) : l ≠ -l := by
  apply ne_of_polarity_ne
  simp only [polarity_negate, ne_eq, Bool.not_eq_not]

@[simp] theorem neg_ne_self (l : L) : -l ≠ l := by
  apply ne_of_polarity_ne
  simp only [polarity_negate, ne_eq, Bool.not_not_eq]

theorem eq_negate_of_var_eq_of_ne {l₁ l₂ : L} : (toVar l₁) = (toVar l₂) → l₁ ≠ l₂ → l₁ = -l₂ := by
  intro hvar hne
  rcases mkPos_or_mkNeg l₁ with (h₁ | h₁)
  · rcases mkPos_or_mkNeg l₂ with (h₂ | h₂)
    · rw [h₁, h₂, hvar] at hne; contradiction
    · rw [h₁, h₂, hvar, negate_mkNeg]
  · rcases mkPos_or_mkNeg l₂ with (h₂ | h₂)
    · rw [h₁, h₂, hvar, negate_mkPos]
    · rw [h₁, h₂, hvar] at hne; contradiction

-- Cayden TODO: there's probably a one-line proof of this
theorem negate_eq_of_var_eq_of_ne {l₁ l₂ : L} : (toVar l₁) = (toVar l₂) → l₁ ≠ l₂ → -l₁ = l₂ := by
  intro h₁ h₂
  have := congrArg (-·) (eq_negate_of_var_eq_of_ne h₁ h₂)
  simp at this
  exact this

theorem eq_trichotomy (l₁ l₂ : L) : l₁ = l₂ ∨ l₁ = -l₂ ∨ (toVar l₁) ≠ (toVar l₂) := by
  by_cases hvar : toVar l₁ = toVar l₂
  · by_cases hpol : polarity l₁ = polarity l₂
    · exact Or.inl (LawfulLitVar.ext _ _ hvar hpol)
    · have := congrArg (-·) (negate_eq_of_var_eq_of_ne hvar (ne_of_polarity_ne hpol))
      simp at this
      exact Or.inr (Or.inl this)
  · exact Or.inr (Or.inr hvar)

@[simp] theorem toPropForm_mkPos (x : ν) : toPropForm (mkPos (L := L) x) = .var x := by
  simp [toPropForm]
@[simp] theorem toPropForm_mkNeg (x : ν) : toPropForm (mkNeg (L := L) x) = .neg (.var x) := by
  simp [toPropForm]

@[simp] theorem mk_toPropForm (l : L) : ⟦toPropForm l⟧ = toPropFun l := by
  dsimp [toPropForm, toPropFun]
  cases polarity l <;> simp

@[simp] theorem toPropFun_mkPos (x : ν) : toPropFun (mkPos (L := L) x) = .var x := by
  simp [toPropFun]
@[simp] theorem toPropFun_mkNeg (x : ν) : toPropFun (mkNeg (L := L) x) = (.var x)ᶜ := by
  simp [toPropFun]
@[simp] theorem toPropFun_neg (l : L) : toPropFun (-l) = (toPropFun l)ᶜ := by
  dsimp [toPropFun]
  aesop

variable [DecidableEq ν]

@[simp] theorem vars_toPropForm (l : L) : (toPropForm l).vars = {toVar l} := by
  dsimp [toPropForm]
  cases polarity l <;> simp [PropForm.vars]

@[simp] theorem semVars_toPropFun (l : L) : (toPropFun l).semVars = {toVar l} := by
  dsimp [toPropFun]
  cases polarity l <;> simp

open PropFun

theorem satisfies_neg {τ : PropAssignment ν} {l : L} :
    τ ⊨ toPropFun (-l) ↔ τ ⊭ toPropFun l := by
  simp [satisfies_iff]

theorem satisfies_set (τ : PropAssignment ν) (l : L) :
    τ.set (toVar l) (polarity l) ⊨ toPropFun l := by
  simp [satisfies_iff, τ.set_get]

theorem eq_of_flip {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊭ toPropFun l → τ.set x p ⊨ toPropFun l → l = mkLit L x p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    simp [hSet, hEq]
  . exfalso; exact h (τ.set_get_of_ne p hEq ▸ hSet)

theorem eq_of_flip' {τ : PropAssignment ν} {l : L} {x : ν} {p : Bool} :
    τ ⊨ toPropFun l → τ.set x p ⊭ toPropFun l → l = mkLit L x !p := by
  simp only [satisfies_iff]
  intro h hSet
  by_cases hEq : x = toVar l
  . rw [hEq, τ.set_get] at hSet
    have : (!p) = polarity l := by
      simp [Bool.bnot_eq, hSet]
    simp [hEq, this]
  . exfalso; exact hSet (τ.set_get_of_ne p hEq ▸ h)

def map [LitVar L V] [LitVar L' V'] (f : V → V') (l : L) : L' :=
  LitVar.mkLit _ (f (LitVar.toVar l)) (LitVar.polarity l)

@[simp] theorem satisfies_map [LitVar L V] [LitVar L' V']
    [LawfulLitVar L' V'] (f : V → V') (l : L) (τ : PropAssignment V')
  : τ ⊨ LitVar.toPropFun (LitVar.map f l : L') ↔ τ.map f ⊨ LitVar.toPropFun l
  := by
  simp [map, toPropFun]
  split <;> simp

end LitVar

/-! ### Clauses -/

abbrev Clause (L : Type u) := Array L

namespace Clause

instance [ToString L] : ToString (Clause L) where
  toString C := s!"({String.intercalate " ∨ " (C.map toString).toList})"

@[simp]
theorem of_append (l₁ l₂ : List L) : { data := l₁ ++ l₂ : Clause L } = { data := l₁ : Clause L } ++ { data := l₂ : Clause L } := by
  show { data := l₁ ++ l₂ : Clause L } = { data := ({data := l₁ : Clause L } ++ { data := l₂ : Clause L }).data }
  simp only [Array.append_data]

@[simp]
theorem of_singleton (l : L) : { data := [l] : Clause L } = #[l] := by
  rfl

@[simp]
theorem of_empty : { data := [] : Clause L } = #[] := by
  rfl

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropForm (C : Clause L) : PropForm ν :=
  C.data.foldr (init := .fls) (fun l φ => (LitVar.toPropForm l).disj φ)

def toPropFun (C : Clause L) : PropFun ν :=
  C.data.foldr (init := ⊥) (fun l φ => (LitVar.toPropFun l) ⊔ φ)

-- Cayden: these cannot be instances because a goal of type (PropForm ν) doesn't
--         contain enough information to "look backward" and find a (Clause L), or
--         vice versa. Encoding L in the type of ν, or vice versa, would help.
-- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/cannot.20find.20synthesization.20order.20for.20instance
--instance : Coe (Clause L) (PropForm ν) := ⟨toPropForm⟩
--instance : Coe (Clause L) (PropFun ν) := ⟨toPropFun⟩

@[simp] theorem mk_toPropForm (C : Clause L) : ⟦C.toPropForm⟧ = C.toPropFun := by
  dsimp [toPropForm, toPropFun]
  induction C.data <;> simp_all

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {C : Clause L} :
    τ ⊨ C.toPropFun ↔ ∃ l ∈ C.data, τ ⊨ LitVar.toPropFun l := by
  rw [toPropFun]
  induction C.data <;> simp_all

theorem tautology_iff' [DecidableEq ν] [LawfulLitVar L ν] (C : Clause L) :
    C.toPropFun = ⊤ ↔ ∃ l₁ ∈ C.data, ∃ l₂ ∈ C.data, l₁ = -l₂ := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    refine not_imp_not.mp ?_
    simp only [not_exists, not_and]
    unfold toPropFun -- :( have to do it because no induction principle for arrays
    induction C.data with
    | nil => simp
    | cons l₀ ls ih =>
      -- crazy list-array induction boilerplate
      have : ls.foldr (init := ⊥) (fun l φ => LitVar.toPropFun l ⊔ φ) = toPropFun ls.toArray := by
        simp [toPropFun]
      simp only [List.foldr_cons, this] at *
      -- end boilerplate
      intro hCompl hEq
      specialize ih fun l₁ h₁ l₂ h₂ => hCompl l₁ (by simp [h₁]) l₂ (by simp [h₂])
      simp only [PropFun.eq_top_iff, satisfies_disj, not_forall] at hEq ih
      have ⟨τ₀, h₀⟩ := ih
      have := hEq τ₀
      have : τ₀ ⊨ LitVar.toPropFun l₀ := by tauto
      let τ₁ := τ₀.set (LitVar.toVar l₀) !(LitVar.polarity l₀)
      have : τ₁ ⊭ LitVar.toPropFun l₀ := by simp [LitVar.satisfies_iff]
      have : τ₁ ⊭ toPropFun ls.toArray := fun h => by
        have ⟨lₛ, hₛ, hτ⟩ := satisfies_iff.mp h
        simp only [satisfies_iff, not_exists, not_and] at h₀
        have : τ₀ ⊭ LitVar.toPropFun lₛ := h₀ lₛ hₛ
        have : lₛ = LitVar.mkLit L (LitVar.toVar l₀) !(LitVar.polarity l₀) :=
          LitVar.eq_of_flip this hτ
        have : lₛ = -l₀ := by simp [this]
        simp at hₛ
        apply hCompl lₛ (List.mem_cons_of_mem _ hₛ) l₀ (List.mem_cons_self _ _) this
      have := hEq τ₁
      tauto
  case mpr =>
    intro ⟨l₁, h₁, l₂, h₂, hEq⟩
    ext τ
    rw [satisfies_iff]
    by_cases hτ : τ ⊨ LitVar.toPropFun l₂
    . aesop
    . have : τ ⊨ LitVar.toPropFun l₁ := by
        rw [hEq, LitVar.satisfies_neg]
        assumption
      tauto

theorem tautology_iff [DecidableEq ν] [LawfulLitVar L ν] (C : Clause L) :
    C.toPropFun = ⊤ ↔ ∃ l ∈ C.data, -l ∈ C.data := by
  rw [tautology_iff' C]
  aesop

@[simp]
theorem toPropFun_append (C₁ C₂ : Clause L) : (C₁ ++ C₂).toPropFun = C₁.toPropFun ⊔ C₂.toPropFun := by
  ext; aesop (add norm satisfies_disj, norm satisfies_iff)

@[simp]
theorem toPropFun_singleton (l : L) : Clause.toPropFun #[l] = LitVar.toPropFun l := by
  ext; simp [satisfies_iff]

theorem toPropFun_getElem_lt (C : Clause L) (i : Nat) (h : i < C.size) : LitVar.toPropFun (C[i]'h) ≤ C.toPropFun := by
  apply PropFun.entails_ext.mpr
  intro σ hσ
  exact satisfies_iff.mpr ⟨C[i]'h, C.getElem_mem_data h, hσ⟩

theorem toPropFun_take_lt (C : Clause L) (i : Nat) : toPropFun ⟨C.data.take i⟩ ≤ C.toPropFun := by
  apply PropFun.entails_ext.mpr
  intro σ hσ
  have ⟨l, hl, hl'⟩ := satisfies_iff.mp hσ
  refine satisfies_iff.mpr ⟨l, List.mem_of_mem_take hl, hl'⟩
def or (c1 c2 : Clause L) : Clause L :=
  c1 ++ c2

@[simp] theorem satisfies_or (c1 c2 : Clause L) (τ : PropAssignment ν)
  : τ ⊨ (c1.or c2).toPropFun ↔ τ ⊨ c1.toPropFun ∨ τ ⊨ c2.toPropFun := by
  simp [or, satisfies_iff]

nonrec def map (L') [LitVar L' ν'] (f : ν → ν') (c : Clause L) : Clause L' :=
  c.map (LitVar.map f)

@[simp] theorem satisfies_map [LitVar L' ν'] [LawfulLitVar L' ν'] (f : ν → ν') (c : Clause L) (τ : PropAssignment ν')
  : τ ⊨ (c.map L' f).toPropFun ↔ τ.map f ⊨ c.toPropFun
  := by
  simp [map, satisfies_iff]

variable [DecidableEq ν]

theorem mem_vars (C : Clause L) (x : ν) :
    x ∈ C.toPropForm.vars ↔ ∃ l ∈ C.data, x = LitVar.toVar l := by
  rw [toPropForm]
  induction C.data <;> simp [*, PropForm.vars]

end Clause

/-! ### CNF -/

abbrev Cnf (L : Type u) := Array (Clause L)

namespace Cnf

instance [ToString L] : ToString (Cnf L) where
  toString C := s!"{String.intercalate " ∧ " (C.map toString).toList}"

variable {L : Type u} {ν : Type v} [LitVar L ν]

def toPropForm (φ : Cnf L) : PropForm ν :=
  φ.data.foldr (init := .tr) (fun l φ => l.toPropForm.conj φ)

def toPropFun (φ : Cnf L) : PropFun ν :=
  φ.data.foldr (init := ⊤) (fun l φ => l.toPropFun ⊓ φ)

@[simp] theorem mk_toPropForm (φ : Cnf L) : ⟦φ.toPropForm⟧ = φ.toPropFun := by
  simp only [toPropForm, toPropFun]
  induction φ.data <;> simp_all

open PropFun

theorem satisfies_iff {τ : PropAssignment ν} {φ : Cnf L} :
    τ ⊨ φ.toPropFun ↔ ∀ C ∈ φ.data, τ ⊨ C.toPropFun := by
  rw [toPropFun]
  induction φ.data <;> simp [*]

variable [DecidableEq ν]

theorem mem_vars (φ : Cnf L) (x : ν) :
    x ∈ φ.toPropForm.vars ↔ ∃ C ∈ φ.data, x ∈ C.toPropForm.vars := by
  simp_rw [toPropForm]
  induction φ.data <;>
    simp_all [PropForm.vars, Clause.mem_vars]

def addClause (C : Clause L) (f : Cnf L) : Cnf L := f.push C

@[simp] theorem satisfies_addClause (C : Clause L) (f : Cnf L) (τ : PropAssignment _)
  : τ ⊨ (f.addClause C).toPropFun ↔ τ ⊨ f.toPropFun ⊓ C.toPropFun
  := by
  simp [satisfies_iff, Array.mem_def, addClause]; aesop

def and (f1 f2 : Cnf L) : Cnf L := f1 ++ f2

@[simp] theorem satisfies_and (f1 f2 : Cnf L) (τ : PropAssignment _)
  : τ ⊨ (f1.and f2).toPropFun ↔ τ ⊨ f1.toPropFun ⊓ f2.toPropFun
  := by
  simp [satisfies_iff, Array.mem_def, and]; aesop

def not (c : Clause L) : Cnf L :=
  Array.map (fun l => #[-l]) c

@[simp] theorem satisfies_not (c : Clause L) (τ : PropAssignment _) [LawfulLitVar L ν]
  : τ ⊨ (not c).toPropFun ↔ ¬ τ ⊨ c.toPropFun
  := by
  simp [satisfies_iff, Clause.satisfies_iff, LitVar.satisfies_iff,
    not, Array.mem_def, Bool.eq_not_iff]

def all (ls : Array L) : Cnf L :=
  Array.map (fun l => #[l]) ls

@[simp] theorem satisfies_all (ls : Array L) (τ : PropAssignment ν) [LawfulLitVar L ν]
  : τ ⊨ (all ls).toPropFun ↔ ∀ l : L, l ∈ ls → τ ⊨ LitVar.toPropFun l
  := by
  simp [satisfies_iff, Clause.satisfies_iff, LitVar.satisfies_iff,
    all, Array.mem_def]

end Cnf
