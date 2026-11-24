import Mathlib.CategoryTheory.Category.Basic

/-!
# Correspondence of Hopf algebras and affine group schemes in Lean 4 - Introduction

This file contains full working code for the code snippets in the Introduction section.
-/

open CategoryTheory

namespace HopfAlgAffGrpSch.Intro
universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞] {W X Y Z : 𝒞}

lemma comp_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  rw [Category.assoc]

end HopfAlgAffGrpSch.Intro
