/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelProofs
public import JH.Parameters.Certificate
public import JH.Potential.Barrier.ModesSpec
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Fintype.Pi

/-!
# Counting ledgers for the barrier union

Section 3.4 indexes ledgers by direction, a row or column, and a translation mode. Padding the
mode by an extra symbol embeds the keys into a finite product. The single-account exponential
bound is then expressed in terms of `nu` for the union bound.
-/

public section

namespace JH.Graph

open JH.Parameters

/-- Encode the two graph sides by a Boolean in the count of accounts in (22). -/
private def encodeDirection : Direction → Bool
  | .forward => true
  | .backward => false

private theorem encodeDirection_injective : Function.Injective encodeDirection := by
  intro a b h
  cases a <;> cases b <;> simp_all [encodeDirection]

/-- Encode a mode by its list of words, padded with `none` to length $B_{\mathrm{ver}}$. -/
private noncomputable def ledgerEncoding (params : Params) (key : LedgerKey params) :
    Bool × Word params.n × (Fin params.Pi → Option (Word params.n)) :=
  (encodeDirection key.1, key.2.1, fun i ↦ key.2.2.val.toList[i.val]?)

private theorem ledgerEncoding_injective (params : Params) :
    Function.Injective (ledgerEncoding params) := by
  intro left right h
  obtain ⟨a, column, mode⟩ := left
  obtain ⟨b, row, mode'⟩ := right
  have hab : a = b := encodeDirection_injective (congrArg Prod.fst h)
  have hl : column = row := congrArg (fun code ↦ code.2.1) h
  have hcodes : (fun i : Fin params.Pi ↦ mode.val.toList[i.val]?) =
      (fun i : Fin params.Pi ↦ mode'.val.toList[i.val]?) :=
    congrArg (fun code ↦ code.2.2) h
  have lists : mode.val.toList = mode'.val.toList := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < params.Pi
    · exact congrFun hcodes ⟨i, hi⟩
    · have outside (s : Finset (Word params.n)) (hs : s.card ≤ params.Pi) : s.toList[i]? = none :=
        List.getElem?_eq_none (by simpa using hs.trans (Nat.le_of_not_gt hi))
      rw [outside _ mode.property.2, outside _ mode'.property.2]
  have mEq : mode = mode' := Subtype.ext (by simpa using congrArg List.toFinset lists)
  rw [hab, hl, mEq]

/-- The finite collection of account keys counted in the union bound (22). -/
@[no_expose] noncomputable instance ledgerKeyFintype (params : Params) :
    Fintype (LedgerKey params) :=
  Fintype.ofInjective (ledgerEncoding params) (ledgerEncoding_injective params)

/-- There are at most $2N(N+1)^{B_{\mathrm{ver}}}$ ledger keys. -/
theorem ledger_count : BarrierModesSpec.LedgerCount := by
  intro params
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (Bool × Word params.n × (Fin params.Pi → Option (Word params.n))) :=
      Fintype.card_le_of_injective (ledgerEncoding params) (ledgerEncoding_injective params)
    _ = _ := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
        Fintype.card_option, word_card params.n, Fintype.card_fin, Params.N, Nat.mul_assoc]

/-- Use `Gamma / Pi = nu` to bound the single-account tail by `2 ^ (-nu / 8)`. -/
theorem ledger_tail_exponent : BarrierModesSpec.TailExponent := by
  intro params hPi
  have hratio : (params.Gamma : ℝ) / (params.Pi : ℝ) = (params.nu : ℝ) := by
    rw [Params.Gamma, Nat.cast_mul]
    field_simp [show (params.Pi : ℝ) ≠ 0 by exact_mod_cast hPi.ne']
  have hlog : Real.log 2 / 8 ≤ Real.log 2 / 2 - 1 / 4 := by
    linarith only [Real.log_two_gt_d9]
  rw [hratio]
  calc
    _ ≤ Real.exp (-((Real.log 2 / 8) * (params.nu : ℝ))) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hlog (by positivity)))
    _ = _ := by
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
      congr 1
      ring

end JH.Graph
