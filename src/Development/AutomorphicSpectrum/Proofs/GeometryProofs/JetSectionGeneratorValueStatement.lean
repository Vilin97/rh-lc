module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionValueOnChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

theorem val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
  have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
    fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
  obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
  have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
      gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
    intro Z f z
    rw [he₀, gm_res f z hW (Set.mem_univ _)]
    exact gm_pull f r z _ (hW (Set.mem_univ _)) _
  refine ⟨e₀, ?_, ?_⟩
  · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
      apply unit_ext
      intro z' _
      obtain ⟨J', hJ', e⟩ := exists_good L hL z'
        (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
        (fun _ _ _ => rfl) (fun κ => h₁ κ _)
      have hv := h₂ z' J' hJ' e
      rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
      have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
        (unitΓ e₀)
      rw [Category.id_comp] at hp
      rw [map_one]
      exact hp.trans hv
    apply toΓ_inj
    rw [map_one]
    exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
  · intro z J _ hc
    rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem aug_comp_inL (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B).comp
        ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      (algebraMap k B).comp ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have h0 : (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.C a) : Jet k Unit p) =
        algebraMap k (Jet k Unit p) a := rfl
    simp only [RingHom.comp_apply, h0, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply k B (Jet B Unit p), AlgHom.commutes]
    rfl
  · intro i
    have h1 : (inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = dQ B p := by
      change (MvPolynomial.aeval fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    have h2 : (jetAug : Jet B Unit p →ₐ[B] B) (dQ B p) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : B)) (MvPolynomial.X () : MvPolynomial Unit B) = _
      simp
    have h3 : (jetAug : Jet k Unit p →ₐ[k] k)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : k)) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    simp only [RingHom.comp_apply, RingHom.coe_coe, h1, h2, h3, map_zero]

theorem red_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  intro E _ _ _ H X0 t k _ x p y B _ _ hy τ hτ j₀ hj₀
  have h1 : ∀ (κ : Fin 2) (q : Sp (Jet B Unit p)),
      (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) ≫
        (![y.left, (1 : Tm x p ⟶ t.G).left] : Fin 2 → _) κ) q ∈ t.PP.L.U j₀ := by
    intro κ q
    rw [Scheme.Hom.comp_apply]
    fin_cases κ
    · exact jet_left_mem t x j₀ hj₀ y hy _
    · exact jet_left_mem t x j₀ hj₀ 1 (by simp [Hom.one_def]) _
  have hc : spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫
        spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      spMap (algebraMap k B) ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [aug_comp_inL]
  obtain ⟨e₀, he, hall⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k Unit p)) t.PP.L t.PP.isLB B p (Fin 2)
    ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1] τ
    (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) j₀ h1
    (fun z' J' hG _ => by rw [hc]; exact hτ _ _ z' J' hG)
  exact ⟨e₀, he, fun z J hG hJ => hall z J hG fun κ => hJ _ (h1 κ z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.jet_section_generator_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit <;> assumption)
end
end
