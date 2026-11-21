import Mathlib

open TensorProduct

namespace UpperTheory.V.Loc.Thick

variable {Q E B : Type} [Field Q] [Field E] [CommRing B] [Algebra Q E] [Algebra Q B] [Algebra E B]
  [IsScalarTower Q E B] (π : B →ₐ[E] E)

variable {π}

section

variable {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
  {p : X →ₗ[Q] X'} {Λ : (B →ₗ[E] E) → X →ₗ[Q] X'}

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in

variable [IsScalarTower Q B X] [IsScalarTower Q E X']

omit [IsScalarTower Q E B] in

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] [IsScalarTower Q B X] [IsScalarTower Q E X'] in

end

variable (Q π) in

section Sm

variable {A V : Type} [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V]
  {F P : Type} [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]

variable (V P) in

noncomputable def sm : A ⊗[Q] F →ₗ[Q] Module.End Q (V ⊗[Q] P) :=
  (TensorProduct.homTensorHomMap (RingHom.id Q) V P V P).comp
    (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap
      (Algebra.lsmul Q Q P : F →ₐ[Q] Module.End Q P).toLinearMap)

variable {A' V' : Type} [CommRing A'] [Algebra Q A'] [AddCommGroup V'] [Module A' V'] [Module Q V']
  [IsScalarTower Q A' V']

omit [Algebra Q P] in

end Sm

end UpperTheory.V.Loc.Thick
