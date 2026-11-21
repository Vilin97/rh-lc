module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LieSmooth

section Loc

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]


end Loc

section Emb

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K]

variable {Y : Var F} {φ : F →+* K} (p : Sp K ⟶ Y.X) (hp : p ≫ Y.str = spMap φ)

end Emb

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def stepNorm {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) : ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then grNorm t x (latDR t x) (u τ) ⟨k, h⟩ else 1
  | .inr k => if h : k < (letters Dw).length then
      grNorm t x (latDR t x) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩ else 1

theorem lnStep_false {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ)
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : lnStep t x u p false st = Real.log (stepNorm t x u st) := by
  rcases st with ⟨τ, k⟩ | k <;> simp only [lnStep, stepNorm, lat] <;> split_ifs <;> simp_all

section Tan

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [Field k] {x : Sp k ⟶ X} {n : ℕ}

end Tan

variable (K : Type) [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw)


end Steps

end GlobalTheory.LieSmooth

end
