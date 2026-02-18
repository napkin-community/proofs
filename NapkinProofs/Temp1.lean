variable {A : Type} {R : A → A → Prop} (x : A) (h : Acc R x)

noncomputable def my_rec : ∀ x : A, Acc R x → Nat := @Acc.rec A R (λ _ _ ↦ Nat) (λ _ _ _ ↦ 1)

def inv {x : A} (h : Acc R x) : Acc R x := Acc.intro x (λ _ h' ↦ Acc.inv h h')
example : inv h = h := rfl -- ok
#reduce my_rec x (inv h) -- 1
#reduce my_rec x h -- Acc.rec _ h

-- failure of transitivity
#check (rfl : my_rec x (inv h) = 1) -- ok
#check (rfl : inv h = h) -- ok
#check (rfl : my_rec x (inv h) = my_rec x h) -- ok
#check (rfl : my_rec x h = 1) -- fail

-- failure of SR:
#check @id (my_rec x h = 1) (@id (my_rec x (inv h) = 1) rfl) -- ok
#check @id (my_rec x h = 1) (@id (1 = 1) rfl) -- fail

-- couldn't reproduced the "fooling tactics into producing type incorrect terms" example
