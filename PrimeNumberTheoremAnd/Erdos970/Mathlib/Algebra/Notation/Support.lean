import Mathlib.Algebra.Notation.Support

namespace Erdos970

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : _root_.Function.support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : _root_.Function.support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end Erdos970
