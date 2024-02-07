import Mathlib


section SymFun

open MvPolynomial
open BigOperators

variable (R : Type*) [CommRing R]

def SymmetricFunctionsHomogeneousSubmodule (n : ℕ) := MvPolynomial.weightedHomogeneousSubmodule R (fun (k : ℕ+) => (k : ℕ)) n

def SymmetricFunctions := GradedAlgebra (fun (n : ℕ) => SymmetricFunctionsHomogeneousSubmodule R n)

def degree (n : ℕ+) : ℕ := n

noncomputable section

def elementary (n : ℕ) : MvPolynomial ℕ+ R :=
  if pos : n > 0 then (monomial (Finsupp.single (⟨n, pos⟩ : ℕ+) 1) 1) else 1

example (n : ℕ) : IsWeightedHomogeneous degree (elementary R n) n := by
  rw [elementary]
  split_ifs with h
  apply isWeightedHomogeneous_monomial
  unfold degree
  unfold weightedDegree'
  simp only [LinearMap.toAddMonoidHom_coe, Finsupp.total_single, smul_eq_mul, one_mul]
  rfl
  have nzero : n = 0 := by
    cases n with
    | zero => rfl
    | succ n => exfalso; apply h; apply Nat.succ_pos
  rw [nzero]
  apply isWeightedHomogeneous_one
  done
