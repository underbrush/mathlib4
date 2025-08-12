/-
Copyright (c) 2025 Tom Lindquist. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Lindquist
-/

import Mathlib.Data.FunLike.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Hom.Basic
-- import Mathlib.Combinatorics.SimplicialComplex.Hom
import Mathlib.Combinatorics.SimplicialComplex.Category

/-!
# Order Complex

This file formalizes the `OrderComplex` of a partial order.

## Main definitions

* `SimplicialComplex.OrderComplex V` : The order complex on the partial order `V`.
* `SimplicialComplex.OrderComplex.Hom f` :
  The simplicial map on order complexes induced by the monotone map `f`
* `SimplicialComplex.OrderComplex.order_dual_iso` :
  The isomorphism between `OrderComplex V` and `OrderComplex (Vᵒᵈ)`.
* `SimplicialComplex.Subdivision K` : The barycentric subdivision of `K`.

## Main lemmas

* `order_complex_id`, `order_complex_comp` : Functoriality of the order complex.

-/

namespace SimplicialComplex
open SimplicialComplexCat

/-- The simplicial complex of chains of a partial order `V`. -/
def OrderComplex (V : Type*) [PartialOrder V] : SimplicialComplex V where
  faces := {C | IsChain LE.le C.toSet}
  downward_closed := by intro _ _; simp; exact flip IsChain.mono

namespace OrderComplex

variable {U V W : Type*} [PartialOrder U] [PartialOrder V] [PartialOrder W]
variable [DecidableEq V] [DecidableEq W]

/-- The simplicial map of order complexes induced by a monotone map. -/
def Hom (f : U →o V) : OrderComplex U |>.Hom <| OrderComplex V where
  toFun := f
  map_faces := by
    intro s
    unfold OrderComplex
    simp
    apply IsChain.image
    exact f.monotone

/-- The identity map is preserved. -/
@[simp] lemma order_complex_id
    : Hom OrderHom.id = Hom.id (OrderComplex V) := by
  ext; simp [Hom, Hom.id]

/-- Composition is preserved. -/
@[simp] lemma order_complex_comp {f : U →o V} {g : V →o W}
    : Hom (g.comp f) = (Hom g).comp (Hom f) := by
  ext; simp [Hom, Hom.comp]

/-- The order complex of `V` is isomorphic to the order complex of `Vᵒᵈ`. -/
def order_dual_iso : of (OrderComplex V) ≅ of (OrderComplex (Vᵒᵈ)) :=
  Iso.isoOfEquiv (Equiv.refl _)
    (by intro s hs; simp [OrderComplex, OrderDual] at *; exact IsChain.symm hs)
    (by intro s hs; simp [OrderComplex, OrderDual] at *; exact IsChain.symm hs)

end OrderComplex

/-- The barycentric subdivision of a simplicial complex
  is the order complex on the poset of faces. -/
def Subdivision {V : Type*} (K : SimplicialComplex V) : SimplicialComplex (Face K) :=
  OrderComplex (Face K)

end SimplicialComplex
