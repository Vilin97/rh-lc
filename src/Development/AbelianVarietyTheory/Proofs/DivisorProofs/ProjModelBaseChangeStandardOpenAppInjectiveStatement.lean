module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPointStatement
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPreimageAffineBaseChangeEqSumProducts

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.BaseChangeSpan

theorem exists_sum_mul_of_closure {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T]
    (A : S →+* T) (B : S' →+* T) (h : Subring.closure (Set.range A ∪ Set.range B) = ⊤) (x : T) :
    ∃ (n : ℕ) (a : Fin n → S) (r : Fin n → S'), x = ∑ i, A (a i) * B (r i) := by
  have hx : x ∈ Subring.closure (Set.range A ∪ Set.range B) := h ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨1, fun _ => a, fun _ => 1, by simp⟩
    · exact ⟨1, fun _ => 1, fun _ => r, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n + m, Fin.append a b, Fin.append r t, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | neg y _ hy =>
    obtain ⟨n, a, r, rfl⟩ := hy
    exact ⟨n, fun i => -a i, r, by simp [Finset.sum_neg_distrib]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n * m, fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2,
      fun k => r (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2, ?_⟩
    rw [← finProdFinEquiv.sum_comp, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr (by simp) fun p _ => ?_
    simp only [Equiv.symm_apply_apply, map_mul]
    ring

end GlobalTheory.BaseChangeSpan

namespace GlobalTheory.BaseChangeSpan

theorem sections_preimage_affine_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  intro R R₁ _ _ ρ P p V hV x
  have sq : IsPullback (pullback.snd p (spMap ρ)) (pullback.fst p (spMap ρ)) (spMap ρ) p :=
    (IsPullback.of_hasPullback p (spMap ρ)).flip
  have hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  have hleG : (pullback.fst p (spMap ρ)) ⁻¹ᵁ V ≤
      (pullback.snd p (spMap ρ)) ⁻¹ᵁ ((spMap ρ) ⁻¹ᵁ ⊤) := by simp
  have po := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) hV hle hleG
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have htop : (⊤ : (Sp R₁).Opens) ≤ (spMap ρ) ⁻¹ᵁ ⊤ := by simp
  have hsub : Set.range ((pullback.snd p (spMap ρ)).appLE ((spMap ρ) ⁻¹ᵁ ⊤) _ hleG).hom ⊆
      Set.range (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom ((Sp R₁).presheaf.map (homOfLE htop).op y), ?_⟩
    rw [RingHom.comp_apply]
    change ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (pullback.snd p (spMap ρ)).appLE ⊤ _ le_top).hom ((Sp R₁).presheaf.map (homOfLE htop).op y) = _
    rw [Iso.hom_inv_id_assoc, ← CommRingCat.comp_apply]
    have h := Scheme.Hom.map_appLE (pullback.snd p (spMap ρ))
      (V := (pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top (homOfLE htop).op
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) y
  obtain ⟨n, a, r, hx⟩ := exists_sum_mul_of_closure ((pullback.fst p (spMap ρ)).app V).hom
    (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom)
    (by
      rw [eq_top_iff, ← hcl]
      exact Subring.closure_mono (Set.union_subset (hsub.trans Set.subset_union_right)
        Set.subset_union_left))
    x
  exact ⟨n, a, r, hx⟩

end GlobalTheory.BaseChangeSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPreimageAffineBaseChangeEqSumProductsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.sections_preimage_affine_baseChange_eq_sum_products : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  first | exact @GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | exact GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum | (intros; apply GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulEqZeroOfFlatLinearlyDisjointSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory.Desc

theorem tmul_sum_eq_zero_of_linDisj {R R₁ F K : Type} [CommRing R] [CommRing R₁] [Field F] [Field K] [Algebra R R₁]
    [Algebra R F] (c : R₁ →+* K) (θ : F →+* K) (hc₀ : Function.Injective (algebraMap R F))
    (hθ : θ.comp (algebraMap R F) = c.comp (algebraMap R R₁)) (hL : LinDisj (algebraMap R F) c θ) :
    ∀ (n : ℕ) (u : Fin n → F) (r : Fin n → R₁), ∑ i, θ (u i) * c (r i) = 0 → ∑ i, u i ⊗ₜ[R] r i = 0 := by
  have hθ' : ∀ b : R, θ (algebraMap R F b) = c (algebraMap R R₁ b) := fun b => RingHom.congr_fun hθ b
  intro n
  induction n with
  | zero => intro u r _; simp
  | succ n ih =>
    intro u r h
    by_cases hind : ∀ b : Fin (n+1) → R, ∑ i, algebraMap R F (b i) * u i = 0 → b = 0
    · have hr := hL (n+1) u hind r (by rw [← h]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      subst hr; simp
    · push_neg at hind
      obtain ⟨b, hb, hb0⟩ := hind
      obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hb0 (funext hc)
      have hdj : algebraMap R F (b j) ≠ 0 := by
        intro h0; apply hj; apply hc₀; rw [h0, map_zero]
      obtain ⟨w, hw⟩ : ∃ w : Fin n → F, ∀ i, w i = u (j.succAbove i) / algebraMap R F (b j) := ⟨_, fun _ => rfl⟩
      have hrel : algebraMap R F (b j) * u j +
          ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i) = 0 := by
        rw [← Fin.sum_univ_succAbove (fun i => algebraMap R F (b i) * u i) j]; exact hb
      have hu : ∀ i, u (j.succAbove i) = b j • w i := by
        intro i; rw [Algebra.smul_def, hw i]; field_simp
      have hsum : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i = - u j := by
        have : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i =
            (∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i)) / algebraMap R F (b j) := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
        rw [this, eq_neg_of_add_eq_zero_right hrel]; field_simp
      have huj : u j = - ∑ i : Fin n, b (j.succAbove i) • w i := by
        simp only [Algebra.smul_def]; rw [hsum, neg_neg]
      have key : ∑ i, u i ⊗ₜ[R] r i =
          ∑ i : Fin n, w i ⊗ₜ[R] (b j • r (j.succAbove i) - b (j.succAbove i) • r j) := by
        rw [Fin.sum_univ_succAbove _ j]
        simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.smul_tmul, ← hu]
        rw [huj, TensorProduct.neg_tmul, TensorProduct.sum_tmul]
        abel
      rw [key]
      apply ih
      have e1 : ∀ i, θ (w i) * c (b j • r (j.succAbove i) - b (j.succAbove i) • r j) =
          θ (u (j.succAbove i)) * c (r (j.succAbove i)) - c (r j) * θ (algebraMap R F (b (j.succAbove i)) * w i) := by
        intro i
        rw [hu i]
        simp only [Algebra.smul_def, map_sub, map_mul, hθ']
        ring

      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum, map_neg]
      have h' := h
      rw [Fin.sum_univ_succAbove _ j] at h'
      linear_combination h'

theorem tmul_sum_eq_zero_of_flat_linDisj : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  intro R R₁ A F K _ _ _ _ _ _ _ hflat c₀ e c θ hc₀ he hec hθ hL n a r h
  letI : Algebra R F := c₀.toAlgebra
  let eA : A →ₐ[R] F := { e with commutes' := fun x => RingHom.congr_fun hec x }
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := R₁) eA.toLinearMap he
  apply hinj

  rw [map_sum, map_zero]
  simp only [LinearMap.rTensor_tmul]
  exact tmul_sum_eq_zero_of_linDisj (R := R) c θ hc₀ hθ hL n (fun i => e (a i)) r h

end GlobalTheory.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulEqZeroOfFlatLinearlyDisjointSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.sum_tmul_eq_zero_of_flat_linearlyDisjoint_subring : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  first | exact @GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | exact GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | (intros; apply GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppInjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.BaseInj

theorem fnOf_appLE_top {Y S : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ S) (U : Y.Opens) (e : U ≤ q ⁻¹ᵁ ⊤)
    (h : genericPoint Y ∈ U) (x : Γ(S, ⊤)) :
    fnOf U h ((q.appLE ⊤ U e).hom x) = fnOf ⊤ trivial (q.appTop.hom x) :=
  fnOf_resG (X := Y) (U := ⊤) (V := U) le_top h (q.appTop.hom x)

theorem app_appLE_top {Y Z S : Scheme.{0}} (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens) (x : Γ(S, ⊤)) :
    (f.app U).hom ((s.appLE ⊤ U le_top).hom x) = ((f ≫ s).appLE ⊤ (f ⁻¹ᵁ U) le_top).hom x := by
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun t => t.hom x) (Scheme.Hom.appLE_comp_appLE f s ⊤ U (f ⁻¹ᵁ U) le_top le_rfl)

theorem fnOf_app_appLE_top {Y Z S : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens)
    (h : genericPoint Y ∈ f ⁻¹ᵁ U) (x : Γ(S, ⊤)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((s.appLE ⊤ U le_top).hom x)) = fnOf ⊤ trivial ((f ≫ s).appTop.hom x) :=
  (congrArg _ (app_appLE_top f s U x)).trans (fnOf_appLE_top (f ≫ s) (f ⁻¹ᵁ U) le_top h x)

theorem const_agree {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P Z : Scheme.{0}} (p : P ⟶ Sp R)
    (g : Z ⟶ P) (s : Z ⟶ Sp R₁) (w : g ≫ p = s ≫ spMap ρ) (V : P.Opens) (r : R) :
    (g.app V).hom ((p.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r)) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r) =
      (spMap ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) :=
    congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  rw [h1, app_appLE_top, w]
  rfl

theorem app_injective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Injective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ _ ρ hρ hc Y _ _ _ q θ D₁ hθ hld _ _ m hff hloc hm k hk b hb
  by_cases hb0 : b = 0
  · have hV : Dp k b = ⊥ :=
      eq_bot_iff.2 fun x hx => ((hM.gen k hk b hb).1 (gen_mem hx) hb0).elim
    rw [hV]
    have : Subsingleton Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ (⊥ : P.Opens)) :=
      inferInstanceAs (Subsingleton Γ(pullback p (spMap ρ), ⊥))
    exact fun _ _ _ => Subsingleton.elim _ _
  have hV : genericPoint P ∈ Dp k b := (hM.gen k hk b hb).2 hb0
  have hY : genericPoint Y ∈ m ⁻¹ᵁ Dp k b :=
    (hloc k hk b hb _).2 (CartierDiv.generatesAt_genericPoint _ ((map_ne_zero θ).2 hb0))
  generalize hf : pullback.lift m q hm = f
  have hf1 : f ≫ pullback.fst p (spMap ρ) = m := by rw [← hf, pullback.lift_fst]
  have hf2 : f ≫ pullback.snd p (spMap ρ) = q := by rw [← hf, pullback.lift_snd]
  clear hf hm hloc
  subst hf1 hf2
  refine (injective_iff_map_eq_zero (f.app _).hom).2 fun x hx => ?_
  obtain ⟨n, a, r, rfl⟩ := GlobalTheory.T.sections_preimage_affine_baseChange_eq_sum_products R R₁ ρ P p (Dp k b) (hM.affine k hk b hb) x
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R Γ(P, Dp k b) :=
    ((p.appLE ⊤ (Dp k b) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  have hsum : ∑ i, θ ((ψ.comp (fnOf (Dp k b) hV)) (a i)) * GlobalTheory.Desc.cst (f ≫ pullback.snd p (spMap ρ)) (r i) = 0 := by
    have := congrArg (fnOf (f ⁻¹ᵁ (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY) hx

    rw [map_zero, map_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul]
    congr 1
    · exact (GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint P Y _ _ hff (Dp k b) hV hY (a i)).symm
    · exact (fnOf_app_appLE_top f _ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY _).symm
  have hz := GlobalTheory.T.sum_tmul_eq_zero_of_flat_linearlyDisjoint_subring R R₁ Γ(P, Dp k b) F Y.functionField hρ c₀ (ψ.comp (fnOf (Dp k b) hV)) _ θ hc
    (ψ.injective.comp (fnOf_injective _ hV))
    (by
      rw [← hM.const]
      ext t
      exact congrArg ψ (fnOf_appLE_top p _ le_top hV _)) hθ hld n a r hsum
  let g := (pullback.fst p (spMap ρ)).app (Dp k b)
  let s : R₁ →+* Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  letI : Algebra R Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (s.comp ρ).toAlgebra
  let gA : Γ(P, Dp k b) →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ⟨g.hom, fun t => const_agree ρ p _ _ pullback.condition _ t⟩
  let sA : R₁ →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := ⟨s, fun _ => rfl⟩
  have := congrArg (Algebra.TensorProduct.lift gA sA fun _ _ => Commute.all _ _) hz

  rw [map_zero, map_sum] at this
  simp only [Algebra.TensorProduct.lift_tmul] at this
  exact this

end GlobalTheory.Desc.BaseInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppInjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.proj_model_baseChange_standard_open_app_injective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Injective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  first | exact @GlobalTheory.Desc.BaseInj.app_injective | exact GlobalTheory.Desc.BaseInj.app_injective | (intros; apply GlobalTheory.Desc.BaseInj.app_injective <;> assumption)
end
end
