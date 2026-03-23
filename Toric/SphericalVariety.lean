/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Spherical varieties

This file defines a spherical variety over `B` over a ring `R` as a scheme `X` over `Spec R`
equipped with an action `B × X → X` with an open orbit.

## TODO

This is very experimental. Many conditions are missing.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ} {X Y : Scheme}

variable (R n)
/-- A spherical variety over `B` over a ring `R` is a scheme `X` equipped with an action `B × X → X`
with an open dense orbit. -/
-- TODO: Add correct assumptions on `B`
class SphericalVariety (B X : Scheme) [B.Over (Spec R)] [X.Over (Spec R)]
    [MonObj (B.asOver (Spec R))] extends ModObj (B.asOver (Spec R)) (X.asOver (Spec R)) where
  -- TODO: Add the open dense orbit assumption

end AlgebraicGeometry
