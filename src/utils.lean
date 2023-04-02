lemma dite_left {α : Sort _} {P : Prop} [decidable P] {a : α} (H : P) {A : P → α} {B : ¬P → α} : 
  dite P A B = A H := begin
    simp *,
  end
lemma dite_right {α : Sort _} {P : Prop} [decidable P] {a : α} (H : ¬P) {A : P → α} {B : ¬P → α} : 
  dite P A B = B H := begin
    simp *,
  end
lemma ite_left {α : Sort _} {P : Prop} [decidable P] {a : α} (H : P) {A : α} {B : α} : 
  ite P A B = A := begin simp *, end
lemma ite_right {α : Sort _} {P : Prop} [decidable P] {a : α} (H : ¬P) {A : α} {B : α} : 
  ite P A B = B := begin simp *, end