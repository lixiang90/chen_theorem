/-
Adapted from PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/
import Mathlib.Algebra.Notation.Support

set_option autoImplicit true

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
