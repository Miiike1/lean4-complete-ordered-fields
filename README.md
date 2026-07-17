# Formalization of the Uniqueness of Complete Ordered Fields in Lean 4

This repository contains the formal verification code developed for my Bachelor's Thesis (Trabajo de Fin de Grado) in Mathematics at the University of Zaragoza.

The project serves as an introduction to the formal foundations of **Lean 4**, a interactive theorem prover and programming language designed for the formal verification of mathematical results. 

---

## 🎯 Objectives

The thesis and this repository focus on three main goals:
1. **Framework Introduction:** Introduce the logical and formal foundations underlying Lean 4.
2. **Practical Guide:** Provide a basic introduction to the basic use of Lean4.
3. **Case Study:** Present a complete, verified case study in formalized mathematics.

---

## 🏆 Main Result

As a practical application, this repository includes a complete formal proof of the following classical algebraic theorem:

> **Theorem:** Any two complete ordered fields satisfying the least upper bound property are isomorphic.

The formalization rigorously follows the standard mathematical construction of the unique field isomorphism between complete ordered fields, verifying every single deductive step within Lean 4.

---

## 📂 Repository Contents & Structure

* **Foundations & Guides:**
  * Introduction to the foundations of Lean 4.
  * Basic examples and proof techniques.
  * Guide to theorem declaration and proof construction.
* **Formalization Core:**
  * Formalization of ordered fields and completeness.
  * Complete proof of the uniqueness (up to isomorphism) of complete ordered fields.

### 💻 Source Code
The core mathematical development can be found in:
* **File:** [`Isomorphism_btw_realfields.lean`](https://github.com/Miiike1/proyecto/blob/master/Isomorphism_btw_two_RealFields/Isomorphism_btw_realfields.lean)

### 📄 Thesis Document
* The complete Bachelor's thesis can be read (in Spanish) in the file: [`Formalización_de_teoremas_A(1).pdf`](https://github.com/Miiike1/proyecto/blob/master/Formalizaci%C3%B3n_de_teoremas_A%20(1).pdf)

---

> 📚 **References:** The development relies heavily on the Lean 4 ecosystem and the [Mathlib](https://github.com/leanprover-community/mathlib4) library.

---

## ✍️ Authorship

* **Author:** Miguel Laborda Velázquez  
* **Supervisor:** Miguel Ángel Marco Buzunáriz  
* **Institution:** University of Zaragoza (Universidad de Zaragoza)  
* **Degree:** Bachelor's Thesis in Mathematics
