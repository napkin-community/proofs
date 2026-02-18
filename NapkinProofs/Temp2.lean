import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Class

abbrev α.{u} := ZFSet.{u}

theorem extensionality : ∀x y : α, (∀z, z ∈ x ↔ z ∈ y) → x = y := by
  intro x y
  exact ZFSet.ext

theorem null_set : ∃a : α, ∀x, x ∉ a := by
  use ZFSet.empty
  exact ZFSet.notMem_empty

theorem pairing : ∀x y, ∃a : α, ∀z, z ∈ a ↔ z = x ∨ z = y := by
  intro x y
  use {x, y}
  intro z
  exact ZFSet.mem_pair

theorem union : ∀x : α, ∃y : α, ∀u, u ∈ y ↔ ∃z ∈ x, u ∈ z := by
  intro x
  use ZFSet.sUnion x
  intro y
  exact ZFSet.mem_sUnion

-- TODO: p 의 타입이 α → Prop 로 잘못 정의되어있음 (Lean의 메타씨오리를 활용한 술어), preds 인 α로 정의를 바꿔야함 (ZFC 내의 술어)
theorem separation : ∀(p : α → Prop) (a : α), ∃b : α, ∀x, x ∈ b ↔ x ∈ a ∧ p x := by -- a.k.a. specification, comprehension
  intro p a
  use ZFSet.sep p a
  intro x
  exact ZFSet.mem_sep

-- TODO: f 가 α → α 로 잘못 정의되어있음 (Lean의 메타씨오리를 활용한 함수), funs 인 α로 정의를 바꿔야함 (ZFC 내의 함수)
theorem replacement : ∀(f : α.{u} → α.{u}) [ZFSet.Definable₁ f] (a : α), ∃b : α, ∀y, y ∈ b ↔ ∃x ∈ a, f x = y := by
  intro f _ a
  use ZFSet.image f a
  intro y
  exact ZFSet.mem_image

theorem powerset : ∀x, ∃y : α, ∀z, z ∈ y ↔ z ⊆ x := by
  intro x
  use ZFSet.powerset x
  intro z
  exact ZFSet.mem_powerset

theorem infinity : ∃x : α, ∅ ∈ x ∧ ∀y ∈ x, y ∪ {y} ∈ x := by
  use ZFSet.omega
  constructor
  ·
    exact ZFSet.omega_zero
  ·
    intro y
    have succ : y ∪ {y} = insert y y := by aesop
    rw [succ]
    exact ZFSet.omega_succ

-- NOTE: 여기에서 Class 를 사용하지 않고는 증명을 못하겠는데 원래 이런건지 궁금함
theorem choice : ∀x : α, ∅ ∉ x → ∃f : α, ∀a ∈ x, f ′ a ∈ (a : Class) := by
  intro x h
  use ZFSet.choice x
  intro a ha
  exact ZFSet.choice_mem x h a ha

theorem regularity : ∀x : α, x ≠ ∅ → ∃y ∈ x, x ∩ y = ∅ := ZFSet.regularity

#print axioms extensionality  -- [propext, Quot.sound]
#print axioms null_set        -- [propext]
#print axioms pairing         -- [propext, Quot.sound]
#print axioms union           -- [propext, Quot.sound]
#print axioms separation      -- [propext, Quot.sound]
#print axioms replacement     -- [propext, Quot.sound]
#print axioms powerset        -- [propext, Quot.sound]
#print axioms infinity        -- [propext, Classical.choice, Quot.sound]
#print axioms choice          -- [propext, Classical.choice, Quot.sound]
#print axioms regularity      -- [propext, Classical.choice, Quot.sound]
