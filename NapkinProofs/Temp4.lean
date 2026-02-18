-- Simple IO.mkRef example of 0 + 1 + 2 + ... + 99 = 4950
private def ref_practice : IO Unit := do
  let sum ← IO.mkRef 0
  for i in [0:100] do
    let current ← sum.get
    sum.set (current + i)
  IO.println s!"Hello, {← sum.get}"
#eval ref_practice


-- Simple ST.mkRef example of 0 + 1 + 2 + ... + 99 = 4950
private def st_practice {σ} : ST σ Nat := do
  let sum : ST.Ref σ Nat ← ST.mkRef 0
  for i in [0:100] do
    let current ← sum.get
    sum.set (current + i)
  return ← sum.get
#guard runST (@st_practice) = 4950


-- Simple proof that uses ST.mkRef
private def st_proof_practice {σ} : ST σ Nat := do
  let sum : ST.Ref σ Nat ← ST.mkRef 0
  return ← sum.get
#guard runST @st_proof_practice = 0

example : runST @st_proof_practice = 0 := by
  unfold st_proof_practice
  simp [runST, bind, EStateM.bind]
  split
  next x a a_1 heq =>
    split at heq
    next x_1 a_2 s heq_1 =>
      split at heq
      next x_2 a_3 s_1 heq_2 => sorry
      next x_2 e s_1 heq_2 => simp_all only [reduceCtorEq]
    next x_1 e s heq_1 => simp_all only [reduceCtorEq]
  next x ex a heq =>
    have fwd : False := nomatch ex
    simp_all only


-- Proof of e1 always returning 1 is non-trivial
private def ST.id {σ α : Type} (a : α) : ST σ α := do
  return a

private def e1 {σ} (f : Unit → ST σ Unit) : ST σ Nat := do
  let x : ST.Ref σ Nat ← ST.mkRef 0
  f ⟨⟩
  x.set 1
  f ⟨⟩
  let ret ← x.get
  return ret

private def e2 {σ} (f : Unit → ST σ Unit) : ST σ Nat := do
  f ⟨⟩
  f ⟨⟩
  return 1

private def func {σ}  : ST σ Nat := do
  let g := e1
  g λ_ ↦ do let _ := g ST.id; return ⟨⟩

#guard runST @func = 1

example : runST @func = 1 := by
  unfold func
  simp [runST, bind, EStateM.bind]
  split
  next x a a_1 heq =>
    sorry
  next x ex a heq =>
    have fwd : False := nomatch ex
    simp_all only
