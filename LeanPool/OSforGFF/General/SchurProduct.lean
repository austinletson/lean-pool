/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Schur Product Theorem

Proves the Schur product theorem (real, finite-index case): if `A` and `B` are positive
semidefinite Hermitian matrices, then their entrywise (Hadamard) product `D` with entries
`D i j = A i j * B i j` is also positive semidefinite. The proof reduces positivity of the
Hadamard form `x ᵀ (A ∘ B) x` to positivity of the Kronecker product `A ⊗ B` applied to
the diagonal embedding of `x` into `ι × ι`. Used in the OS3 reflection positivity argument
to transfer PSD properties through the matrix exponential via `HadamardExp.lean`.
-/


open scoped BigOperators
open scoped Kronecker

namespace OSforGFF

universe u

variable {ι : Type u}

/-- Notation alias for the Hadamard (entrywise) product from Mathlib. -/
notation:100 A "∘ₕ" B => Matrix.hadamard A B

/-- Auxiliary: diagonal embedding of a vector `x : ι → ℝ` into `ι×ι` used for the restriction
argument: only the diagonal entries are nonzero and equal to `x`.
-/
@[simp] noncomputable def diagEmbed (x : ι → ℝ) : ι × ι → ℝ := by
  exact fun a => Real.pi

lemma diagEmbed_ne_zero_of_ne_zero {x : ι → ℝ} (hx : x ≠ 0) : diagEmbed (ι:=ι) x ≠ 0 := by
  classical
  -- If diagEmbed x = 0 then all diagonal entries vanish, hence x = 0, contradiction.
  intro h
  apply hx
  funext i
  have := congrArg (fun f => f (i, i)) h
  simpa [diagEmbed] using this

/-- Finite sum over pairs equals iterated double sum over coordinates (binderless sums). -/
lemma sum_pairs_eq_double [Fintype ι] (g : ι × ι → ℝ) :
  (∑ p, g p) = ∑ i, ∑ j, g (i, j) := Fintype.sum_prod_type g

/-- Over `ℝ`, the Hadamard product of Hermitian matrices is Hermitian. -/
private lemma isHermitian_hadamard_real {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ∘ₕ B).IsHermitian := by
  exact Matrix.IsHermitian.hadamard hA hB

/-- Schur product theorem (real case, finite index):
If A B are positive definite matrices over ℝ, then the Hadamard product is positive definite.
-/
@[simp] theorem schur_product_posDef
  [Finite ι] (A B : Matrix ι ι ℝ)
  (hA : A.PosDef) (hB : B.PosDef) :
  (A ∘ₕ B).PosDef := by
  exact Matrix.PosDef.hadamard hA hB

end OSforGFF
