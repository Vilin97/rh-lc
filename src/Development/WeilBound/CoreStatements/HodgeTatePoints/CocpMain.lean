module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLiftStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiff
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PairEvaluation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitsMulRelationRearrangeCommRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.WeilBound.CoreStatements.HodgeTatePoints.QamCore
import Mathlib.RingTheory.Coalgebra.IsFrobenius

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.alpha_kernel_derivative_vanishes : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv (R := R) ((0 : Fin 2), i) g)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Kill.germKill | exact GlobalTheory.CompanionTheory.Ar.Kill.germKill | (intros; apply GlobalTheory.CompanionTheory.Ar.Kill.germKill <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestriction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Ring

variable (B : Type) [CommRing B] (p : ℕ)

theorem X_pow_dvd_of_mem {P : MvPolynomial Unit B} (hP : P ∈ orig B Unit ^ (p + 1)) :
    (Polynomial.X : Polynomial B) ^ (p + 1) ∣ MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P := by
  have h₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P ∈
      Ideal.map ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
        MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (orig B Unit ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h₁
  have h₂ : Ideal.span (Set.range fun i : Unit => ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
      MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (MvPolynomial.X i)) =
      Ideal.span {(Polynomial.X : Polynomial B)} := by
    congr 1
    ext a
    simp
  rw [h₂, Ideal.span_singleton_pow] at h₁
  exact Ideal.mem_span_singleton.1 h₁

variable {B p}

theorem top_coeff_eq (hp : 1 ≤ p) (b : Fin (p + 1) → B) (v : B)
    (h : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v) : b (Fin.last p) = v := by
  set P : MvPolynomial Unit B := ∑ i : Fin (p + 1), MvPolynomial.C (b i) * MvPolynomial.X () ^ (i : ℕ) -
    (1 + MvPolynomial.X () ^ p * MvPolynomial.C v) with hPdef
  have hP : P ∈ orig B Unit ^ (p + 1) := by

    rw [← Ideal.Quotient.eq_zero_iff_mem, hPdef, map_sub, map_add (f := _), map_sum, map_one, map_mul, map_pow, sub_eq_zero]
    simp only [map_mul, map_pow]
    exact h
  have hd := X_pow_dvd_of_mem B p hP
  have hc := Polynomial.X_pow_dvd_iff.1 hd p (Nat.lt_succ_self p)
  have hp0 : p ≠ 0 := by omega
  have e₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P =
      ∑ i : Fin (p + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ) -
        (1 + Polynomial.C v * Polynomial.X ^ p) := by

    simp only [hPdef, map_sub, map_add (f := _), map_sum, map_mul, map_pow, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Polynomial.algebraMap_eq]
    ring
  have e₂ : ∑ i : Fin (p + 1), (if p = (i : ℕ) then b i else 0) = b (Fin.last p) := by
    rw [Finset.sum_eq_single (Fin.last p)]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro h'
      exact hi (Fin.ext (by simpa using h'.symm))
    · simp
  rw [e₁] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one, if_neg hp0, e₂, if_true, zero_add] at hc
  exact sub_eq_zero.1 hc

end Ring

theorem appLE_top_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (W : Y.Opens) (h₁ : ⊤ ≤ f ⁻¹ᵁ W)
    (h₂ : ⊤ ≤ g ⁻¹ᵁ W) : f.appLE W ⊤ h₁ = g.appLE W ⊤ h₂ := by
  subst e
  rfl

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appTop = f.appLE ⊤ ⊤ h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Test

variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)
variable {B : Type} [CommRing B] [Algebra k B]

theorem rQ_appLE_prZ (p : ℕ) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W)
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W)) (a : Γ(pullback G.hom x, W)) :
    ((rQ G x p z).appLE _ ⊤ hr).hom (((prZ G x p).app W).hom a) =
      ((spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop).hom
        (((xkZ G x z).appLE W ⊤ hW).hom a) := by
  have h₁ : (prZ G x p).app W ≫ (rQ G x p z).appLE _ ⊤ hr = (rQ G x p z ≫ prZ G x p).appLE W ⊤ hr := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have h₂ : (xkZ G x z).appLE W ⊤ hW ≫
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop =
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ xkZ G x z).appLE W ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun y _ => hW (show _ from trivial)) := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ W ⊤ ⊤ hW (by simp), appTop_eq_appLE _ (by simp)]
  have h₃ := h₁.trans ((appLE_top_congr (rQ_prZ G x p z) W _ _).trans h₂.symm)
  exact congrArg (fun q => q.hom a) h₃

theorem rQ_appLE_dltOn (p : ℕ) (z : overAt x B ⟶ G) (V : (Ym G x p).Opens) (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ V) :
    ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = toΓ _ (dQ B p) := by
  have h₁ : (Ym G x p).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (rQ G x p z).appLE V ⊤ hr =
      (rQ G x p z).appTop := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h₂ : ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = ((rQ G x p z).appTop).hom (dlt G x p) :=
    congrArg (fun q => q.hom (dlt G x p)) h₁
  have h₃ := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit p) (Ideal.Quotient.mk _ (MvPolynomial.X ()))))
    (rQ_fst G x p z)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h₃
  rw [h₂, dlt, h₃, spMap_toΓ]
  congr 1
  exact MvPolynomial.aeval_X (R := k) (fun _ : Unit => dQ B p) ()

theorem coef_at_test (p : ℕ) (hp : 1 ≤ p) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens)
    (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B)
    (hf : f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ))
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (hv : ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v)) :
    ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  have hs : ∀ i, ∃ b : B, toΓ B b = ((xkZ G x z).appLE W ⊤ hW).hom (c i) := fun i =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2 _
  choose b hb using hs
  have key : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v := by
    apply toΓ_inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, rQ_appLE_prZ G x p z W hW hr, rQ_appLE_dltOn, ← hb, spMap_toΓ]
    rfl
  rw [← hb, top_coeff_eq hp b v key]

end Test

theorem coef_pull : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  intro X0 G _ k _ x p hp B _ _ z W hW c f v hf hr hv
  exact coef_at_test G x p hp z W hW c f v hf hr hv

end GlobalTheory.CompanionTheory.Ar.Coc
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestrictionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.delta_expansion_restriction : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | exact GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.coef_pull <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiffStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | exact GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.CocpMain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cocp

theorem cocycle_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), alpha g.B p (fun i => w i ^ p) = 0 → ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G))), c.IsGen := by
  intro E _ _ _ H _ hstar X0 t k _ _ p _ _ hp x d g w hα
  obtain ⟨hy0, hy1, -⟩ := PositivityTheory.HtPt.Ce.pt_of_vec E H hstar X0 t k p hp x d g w
  have hwv : (hw g.B p).mulVec (fun i => w i ^ p) = 0 := by
    have := congrArg Prod.fst hα
    rwa [alpha_apply] at this
  have hyp := hy1 hwv
  obtain ⟨gs, hax, hpow, -⟩ := GlobalTheory.T.pow_one_series_p_formula k p d (𝓞 E) g.B
  have hkill := GlobalTheory.T.alpha_kernel_derivative_vanishes k p d (𝓞 E) g.B (fun i => w i ^ p) gs hα hpow
  have hf : ∀ q, MvPowerSeries.pderiv (R := k) q (dSer gs fun i => w i ^ p) = 0 := by
    rintro ⟨i, j⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hkill j
  obtain ⟨hI, hN, hCh, hT⟩ := GlobalTheory.T.formal_germ_jet_lift E H hstar X0 t k p x d g (fun m => xkZ t.G x (g.x m))
    (fun m => xkZ_fst t.G x _) (fun m => xkZ_snd t.G x _)
  obtain ⟨C, hC, hnorm, hB⟩ := GlobalTheory.CompanionTheory.Ar.Coc.Pf.pfold E H hstar X0 t k p x d g w gs hax hpow _ rfl hy0 hyp
  have hL := t.PP.isLB
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨s⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ := by
    have hc := hL.cover
    have : (1 : overAt x k ⟶ t.G).left s ∈ (⊤ : t.G.left.Opens) := trivial
    rw [← hc] at this
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    refine ⟨j, fun s' _ => ?_⟩
    have e : s' = s := Subsingleton.elim (α := Sp k) _ _
    rw [e]
    exact hj
  have hU : ∀ m, ⊤ ≤ xkZ t.G x (g.x m) ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) := by
    intro m q _
    have e : (homAt x (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ g.x m).left = (1 : overAt x k ⟶ t.G).left :=
      congrArg (fun q => q.left) (g.chart.zero m)
    have e₁ : pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) = (g.x m).left q := by
      rw [← Scheme.Hom.comp_apply, xkZ_fst]
    have e₂ : (g.x m).left q = (1 : overAt x k ⟶ t.G).left s := by
      rw [← jet_pt m q s, ← e]
      rfl
    change pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) ∈ t.PP.L.U j₀
    rw [e₁, e₂]
    exact hj₀ trivial
  haveI : Nonempty (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) :=
    ⟨⟨_, hU 0 (show (spMap ((jetAug : Jet k (Fin 1 × Fin d) 0 →ₐ[k] k) : Jet k (Fin 1 × Fin d) 0 →+* k) s) ∈ ⊤ from trivial)⟩⟩
  have main := PositivityTheory.HtPt.Qam.core_firstOrder X0 t.G k x p hp hN t.PP.L hL _ _ (prZ_fst t.G x p).symm (secZ_pa t.G x _ hy0) C hC hnorm j₀
    (fun c h hc => by
      obtain ⟨F, hF1, -, hF3⟩ := hT _ hU (c (Fin.last p))
      refine hF3 (GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff k p d F _ hf fun m => ?_)
      obtain ⟨v, hv⟩ := hB j₀ hj₀ m
      refine ⟨v, ?_⟩
      have hr : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ (prZ t.G x p ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)) := by
        intro q _
        have e : prZ t.G x p (rQ t.G x p (g.x m) q) = xkZ t.G x (g.x m)
            (spMap ((inR (k := k) (Jet k (Fin 1 × Fin d) m) p : Jet k (Fin 1 × Fin d) m →ₐ[k] Jet (Jet k (Fin 1 × Fin d) m) Unit p) : Jet k (Fin 1 × Fin d) m →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) q) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, rQ_prZ]
        change prZ t.G x p (rQ t.G x p (g.x m) q) ∈ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)
        rw [e]
        exact hU m trivial
      have hr' : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![_, _] (fun _ => j₀) :=
        hr.trans fun q hq => h hq
      have h2 := GlobalTheory.T.delta_expansion_restriction X0 t.G k x p hp _ (g.x m) _ (hU m) c _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) hc hr (by
        rw [← hv hr']
        exact congrArg (fun q => q.hom (C.s fun _ => j₀).val) (Scheme.Hom.map_appLE (rQ t.G x p (g.x m)) hr (homOfLE h).op))
      exact toΓ_inj _ ((hF1 m).symm.trans h2))
  rw [trY_pa, trY_pb] at main
  exact main

theorem tanpf_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p :=
  PositivityTheory.HtPt.Ce.tanpf_inj_of cocycle_p

end PositivityTheory.HtPt.Cocp
end
end
