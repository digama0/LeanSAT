/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import LeanSAT.Encode.VEncCNF

/-! ## Tseitin Transform

This file implements a lightly optimized Tseitin encoding
of arbitrary `PropForm` formulas into CNF.

The formula is put into negation normal form first,
and top-level ∧ / top-level ∨ are collected into one
formula/clause respectively.
-/

namespace LeanSAT.Encode.Tseitin

open Model

inductive NegNormForm (L : Type u)
| all (as : Array (NegNormForm L))
| any (as : Array (NegNormForm L))
| tr | fls
| lit (l : L)
deriving Repr

namespace NegNormForm

variable [LitVar L ν]

def toPropFun (r : NegNormForm L) : PropFun ν :=
  match r with
  | .all as => PropFun.all (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .any as => PropFun.any (as.attach.map (fun ⟨x,_h⟩ =>
      toPropFun x)).toList
  | .lit l => LitVar.toPropFun l
  | .tr => ⊤
  | .fls => ⊥

def const (val : Bool) : NegNormForm L :=
  match val with
  | true  => .tr
  | false => .fls

@[simp] theorem const_toPropFun
  : (const b : NegNormForm L).toPropFun = if b then ⊤ else ⊥
  := by ext τ; cases b <;> simp [const, toPropFun]

def ofPropForm (neg : Bool) : PropForm ν → NegNormForm L
| .tr => const (!neg)
| .fls => const neg
| .var v => .lit <| LitVar.mkLit _ v (!neg)
| .neg f => ofPropForm (!neg) f
| .conj a b =>
  if neg then
    .any #[ofPropForm neg a, ofPropForm neg b]
  else
    .all #[ofPropForm neg a, ofPropForm neg b]
| .disj a b =>
  if neg then
    .all #[ofPropForm neg a, ofPropForm neg b]
  else
    .any #[ofPropForm neg a, ofPropForm neg b]
| .impl a b =>
  if neg then
    .all #[ofPropForm false a, ofPropForm true b]
  else
    .any #[ofPropForm true a, ofPropForm false b]
| .biImpl a b =>
  if neg then
    .any #[
      .all #[ofPropForm false a, ofPropForm true b]
    , .all #[ofPropForm false b, ofPropForm true a]
    ]
  else
    .all #[
      .any #[ofPropForm true a, ofPropForm false b]
    , .any #[ofPropForm true b, ofPropForm false a]
    ]

theorem toPropFun_ofPropForm [LawfulLitVar L ν] (f : PropForm ν)
  : toPropFun (L := L) (ofPropForm neg f) =
      if neg then ⟦.neg f⟧ else ⟦f⟧ := by
  induction f generalizing neg
  case tr | fls | var | neg | conj | disj | impl | biImpl =>
    -- we ♥ aesop
    aesop (add norm 1 simp [ofPropForm,toPropFun,himp_eq,PropFun.biImpl_eq_impls,Array.attach])

mutual
def conjuncts : NegNormForm L → Array (NegNormForm L)
| tr => #[]
| fls => #[fls]
| lit l => #[.lit l]
| all as => as.attach.concatMap (fun ⟨a,_h⟩ => conjuncts a)
| any as => #[.any <| as.attach.concatMap (fun ⟨a,_h⟩ => disjuncts a)]

def disjuncts : NegNormForm L → Array (NegNormForm L)
| tr => #[tr]
| fls => #[]
| lit l => #[.lit l]
| any as => as.attach.concatMap (fun ⟨a,_h⟩ => disjuncts a)
| all as => #[.all <| as.attach.concatMap (fun ⟨a,_h⟩ => conjuncts a)]
end

set_option maxHeartbeats 500000 in
set_option pp.proofs.withType false in
mutual
def toPropFun_all_conjuncts : (f : NegNormForm L) → toPropFun (.all (conjuncts f)) = toPropFun f
| tr    => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| fls   => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| lit l => by simp [conjuncts, toPropFun, Array.attach, PropFun.all]
| all as => by
  have : ∀ a ∈ as, _ := fun a _h =>
    toPropFun_all_conjuncts a
  ext τ
  simp_rw [PropFun.ext_iff, imp_forall_iff] at this
  rw [forall_comm] at this
  specialize this τ
  simp (config := {contextual := true})
    [ toPropFun, Array.attach, @eq_comm _ (toPropFun _)
    , ← this]
  clear this
  simp [conjuncts, Array.data_concatMap, Array.attach, Array.mem_def]
  constructor
  · rintro h _ x1 hx1 - rfl - x2 hx2 - -
    apply h _ _ _ hx1 hx2 _ hx1 hx2 rfl
  · rintro h _ x2 x1 hx1 hx2 - - - -
    apply h _ _ hx1 hx1 rfl _ _ hx2 hx2 rfl
| any as => by
  have : ∀ a ∈ as, _ := fun a _h =>
    toPropFun_any_disjuncts a
  ext τ
  simp [toPropFun, conjuncts, Array.data_concatMap, Array.attach, Array.mem_def]
  constructor
  · rintro ⟨b,⟨a,ha,hb⟩,h⟩
    simp_rw [Array.mem_def] at this; specialize this a ha
    use a; rw [← this]
    simp [ha, toPropFun, Array.attach]
    refine ⟨_,⟨b,?_⟩,h⟩
    simp [hb, Array.mem_def]
  · rintro ⟨a,ha,h⟩
    specialize this a; rw [Array.mem_def] at this; specialize this ha
    rw [← this] at h
    simp [toPropFun, Array.attach, Array.mem_def] at h
    rcases h with ⟨b,hb,h⟩
    refine ⟨b,⟨a,ha,hb⟩,h⟩

def toPropFun_any_disjuncts : (f : NegNormForm L) → toPropFun (.any (disjuncts f)) = toPropFun f
| tr    => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| fls   => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| lit l => by simp [disjuncts, toPropFun, Array.attach, PropFun.any]
| any as => by
  have : ∀ a ∈ as, _ := fun a _h =>
    toPropFun_any_disjuncts a
  ext τ
  simp [toPropFun, Array.attach]
  constructor
  · rintro ⟨_,⟨b,hb,-,rfl⟩,h⟩
    simp [disjuncts, Array.data_concatMap, Array.attach] at hb
    rcases hb with ⟨a,ha,ha',hb⟩
    specialize this _ ha'
    refine ⟨_,⟨_,ha,ha',rfl⟩,?_⟩
    rw [← this]; simp [toPropFun]
    refine ⟨b,⟨?_,?_⟩,h⟩
    · simp only [Array.mem_def, hb]
    · simp [Array.attach, hb]
  · rintro ⟨_,⟨a,ha,_,rfl⟩,h⟩
    rw [← this _ ‹_›] at h
    simp [toPropFun] at h
    rcases h with ⟨b,⟨hb,hb'⟩,h⟩
    refine ⟨_, ⟨b,?_⟩, h⟩
    simp [Array.attach] at hb'
    simp [disjuncts, Array.mem_def, Array.data_concatMap, Array.attach]
    refine ⟨_, ha, hb'⟩
| all as => by
  have : ∀ a ∈ as, _ := fun a _h =>
    toPropFun_all_conjuncts a
  ext τ
  simp_rw [PropFun.ext_iff, imp_forall_iff] at this
  rw [forall_comm] at this
  specialize this τ
  simp (config := {contextual := true})
    [ toPropFun, Array.attach, @eq_comm _ (toPropFun _)
    , ← this]
  clear this
  aesop (add simp [toPropFun, conjuncts, disjuncts, Array.attach, Array.mem_def, Array.data_concatMap])
end

def cleanup : NegNormForm L → NegNormForm L
| tr => .tr
| fls => .fls
| lit l => .lit l
| all as =>
  let conj := conjuncts (.all as)
  .all conj
| any as =>
  let disj := disjuncts (.any as)
  .any disj

@[simp] theorem toPropFun_cleanup [LawfulLitVar L ν] (f : NegNormForm L)
  : toPropFun (L := L) (cleanup f) = toPropFun f := by
  apply Eq.symm -- otherwise aesop rewrites in the wrong direction
  cases f <;> simp [cleanup, toPropFun_all_conjuncts, toPropFun_any_disjuncts]


end NegNormForm

open VEncCNF

attribute [local simp] NegNormForm.toPropFun

open PropFun in
/-- Tseitin encoding in the general case creates temporaries for each clause -/
def encodeNNF_mkDefs [LitVar L ν] [LitVar L' ν'] [LawfulLitVar L ν] [DecidableEq ν]
        (t : ν) (emb : ν' ↪ ν) (f : NegNormForm L')
  : VEncCNF L Unit (fun τ => τ t ↔ τ ⊨ f.toPropFun.map emb) :=
  match f with
  | .tr =>
      addClause #[LitVar.mkPos t]
      |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .fls =>
      addClause #[LitVar.mkNeg t]
      |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .lit l =>
      biImpl (LitVar.mkPos t) (LitVar.map emb l)
      |>.mapProp (by simp)
  | .all as =>
      withTemps as.size (
        seq[
          for_all (Array.ofFn id) (fun i =>
            encodeNNF_mkDefs
              (.inr i) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) (as[i.val]'i.isLt)
          )
        , defConj (EncCNF.WithTemps.var (L := L) t) (Array.ofFn (EncCNF.WithTemps.temp (L := L) ·))
        ]
      ) |>.mapProp (by
        ext τ; simp [Array.mem_def, Array.attach]
        simp [List.mem_iff_get]
        constructor
        case a.mp =>
          aesop
        case a.mpr =>
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr i => τ.map emb ⊨ (as[i]).toPropFun
          aesop)
  | .any as =>
      withTemps as.size (
        seq[
          for_all (Array.ofFn id) (fun i =>
            encodeNNF_mkDefs
              (.inr i) (emb.trans ⟨Sum.inl,Sum.inl_injective⟩) (as[i.val]'i.isLt)
          )
        , defDisj (EncCNF.WithTemps.var (L := L) t) (Array.ofFn (EncCNF.WithTemps.temp (L := L) ·))
        ]
      ) |>.mapProp (by
        ext τ; simp [Array.mem_def, Array.attach]
        simp [List.mem_iff_get]
        constructor
        case a.mp =>
          aesop
        case a.mpr =>
          intro h
          open PropFun in
          use fun
            | .inl v => τ v
            | .inr i => τ.map emb ⊨ (as[i]).toPropFun
          aesop)

open PropFun in
def encodeNNF [LitVar L ν] [LawfulLitVar L ν] [DecidableEq ν]
        (f : NegNormForm L) : VEncCNF L Unit (· ⊨ f.toPropFun) :=
  match f with
  | .tr => VEncCNF.pure () |>.mapProp (by funext; simp)
  | .fls => addClause #[] |>.mapProp (by simp [Clause.toPropFun])
  | .lit l => addClause #[l] |>.mapProp (by simp [Clause.toPropFun, PropFun.any])
  | .all fs =>
    for_all (Array.ofFn id) (fun i => encodeNNF (fs[i.val]'i.isLt))
    |>.mapProp (by
      funext τ
      simp [Array.mem_def, Array.attach]
      simp [List.mem_iff_get, Array.getElem_eq_data_get])
  | .any fs =>
    withTemps fs.size (
      seq[
        for_all (Array.ofFn id) (fun i =>
          encodeNNF_mkDefs (.inr i) ⟨Sum.inl, Sum.inl_injective⟩ (fs[i.val]'i.isLt)
        )
      , addClause (Array.ofFn (EncCNF.WithTemps.temp (L := L) ·))
      ]
    ) |>.mapProp (by
      ext τ; simp [Array.mem_def, Array.attach, Clause.satisfies_iff]
      simp [List.mem_iff_get, Array.getElem_eq_data_get]
      constructor
      case a.mp =>
        aesop
      case a.mpr =>
        intro h
        open PropFun in
        use fun
          | .inl v => τ v
          | .inr i => τ ⊨ (fs[i]).toPropFun
        aesop)

-- nospecialize here because otherwise the compiler tries specializing it a ton
-- and that causes big slowdowns when building up VEncCNFs
open PropForm in
@[nospecialize]
def encode [LitVar L V] [LawfulLitVar L V] [DecidableEq V]
      (f : PropForm V) : VEncCNF L Unit (· ⊨ f) :=
  let nnf : NegNormForm L := (NegNormForm.ofPropForm false f).cleanup
  encodeNNF nnf
  |>.mapProp (by simp [NegNormForm.toPropFun_ofPropForm]; rfl)

end Tseitin

open Model.PropForm.Notation in
syntax "tseitin[" propform "]" : term

macro_rules
| `(tseitin[ $t ]) => `(Tseitin.encode [propform| $t ])

example [DecidableEq ν] [LitVar L ν] [LawfulLitVar L ν] (a b : ν)
    : VEncCNF (ν := ν) L Unit (fun τ => τ a ∧ τ b) :=
  tseitin[ {a} ∧ {b} ]
  |>.mapProp (by simp)
