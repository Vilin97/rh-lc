module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

end GlobalTheory.ShFam.BdArc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  first | exact @GlobalTheory.HolArc.exists_holPts_ne_zero | exact GlobalTheory.HolArc.exists_holPts_ne_zero | (intros; apply GlobalTheory.HolArc.exists_holPts_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto

section

@[expose] public section

open GlobalTheory.ShFam.BdArc Filter Topology

namespace GlobalTheory.ShFam.BdArc

theorem exists_complexPoint_of_notMem {F A : Type} [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    (σ : F →+* ℂ) (P : Ideal A) [hP : P.IsPrime] {s : A} (hs : s ∉ P) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ψ s ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have hj : P.jacobson = P := IsJacobsonRing.out inferInstance hP.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hs
  push Not at hs
  obtain ⟨M, ⟨hle, hM⟩, hsM⟩ := hs
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite F (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)
  let _ : Algebra F ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩
  · ext x
    exact (κ.comp (Ideal.Quotient.mkₐ F M)).commutes x
  · show κ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]
  · show κ (Ideal.Quotient.mk M s) ≠ 0
    rw [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM

theorem dvd_or_dvd_of_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a b : A) :
    (∃ s, s ∉ P ∧ a ∣ s * b) ∨ ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)
  have key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y := by
    rintro x y ⟨c, hc⟩
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨d, d.2, n, ?_⟩
    apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    simp only at hnd
    rw [map_mul, map_mul, hc, ← hnd]
    ring
  exact (ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)

theorem exists_eq_mul_pow_of_tendsto_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ p a m hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m := by
    rintro P _ hpP s hs ⟨t, ht⟩
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := exists_complexPoint_of_notMem σ P hs
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ m) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]
    exact hs0 (tendsto_nhds_unique (hc s) h2)
  obtain ⟨b, hb⟩ : p ^ m ∣ a := by
    refine GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_
    refine (dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_
    rintro ⟨s, hs, hd⟩
    exact key P (hP.mem_of_pow_mem m hpm) s hs hd
  refine ⟨b, by rw [hb, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  by_contra hbP
  exact key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩

end GlobalTheory.ShFam.BdArc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
open GlobalTheory.ShFam.BdArc GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.CompHS

theorem evalPt_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (ψ : Γ(X, U) →+* R) (h : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) ⁻¹ᵁ U) :
    GlobalTheory.TangentOrigin.evalPt (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) U h = ψ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem exists_extension_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  intro E _ _ _ H Dw l Xo c Y X Z la σ m hm W hW i p hi hdom hsm hp hbd
  have hPW : (Y₀ X Z).basicOpen p ≤ W := (Y₀ X Z).basicOpen_le p
  have hPU : (Y₀ X Z).basicOpen p ≤ U₀ X Z := fun y hy => by
    by_contra h
    exact (hbd y (hPW hy)).1 h hy
  have hPL : (Y₀ X Z).basicOpen p ≤ U₀ X Z ⊓ (L₀ X Z la).U i := le_inf hPU (hPW.trans hi)
  have := hW.isLocalization_basicOpen p
  obtain ⟨⟨a, _, M, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) (resG _ hPL (m.loc i))
  have e' : resG _ hPL (m.loc i) * resG _ hPW (p ^ M) = resG _ hPW a := e
  have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)) =
      (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z := Spec.map_preimage _
  letI : Algebra c.F Γ(Y₀ X Z, W) :=
    (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom.toAlgebra
  obtain ⟨b, hab, hb⟩ := exists_eq_mul_pow_of_tendsto_zero c.F Γ(Y₀ X Z, W) hsm σ p a M hp
    fun ψ r hψ hσ h0 h1 => by
      have hlim := hm W hW i hi ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hbd _ (spMap_fromSpec_mem hW _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hW _ p s).1 h h0)
        (fun u hu hu0 s _ => hPU ((spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hu hu0)))
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hψ.1
      filter_upwards [hlim ε hε, mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hub hu0
      have hWx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ W :=
        fun s _ => spMap_fromSpec_mem hW _ s
      have hPx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (Y₀ X Z).basicOpen p :=
        fun s _ => (spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hub hu0)
      have hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z :=
        fun s hs => hPU (hPx hs)
      have hiu : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i :=
        fun s hs => hi (hWx hs)
      have hev := evalPt_spMap_fromSpec hW (ψ u) hWx
      have hpu : ψ u (p ^ M) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (h1 u hub hu0)
      have hmul : H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hiu m * ψ u (p ^ M) =
          ψ u a := by
        have e₁ := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hPx) e'
        rw [map_mul, GlobalTheory.TangentOrigin.evalPt_res _ hPL (GlobalTheory.TopForm.le_preimage_inf hO hiu) hPx,
          GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, hev] at e₁
        exact e₁
      rw [dist_zero_right, ← hmul, mul_div_cancel_right₀ _ hpu]
      exact hu hO hiu
  refine ⟨b, fun y' h h' => ?_, fun y' h hy => ?_⟩
  · have hyP : y' ∈ (Y₀ X Z).basicOpen p := by
      by_contra hn
      exact (hbd y' h).2 hn h'
    have hunit : IsUnit (ger y' h p) := ((Y₀ X Z).mem_basicOpen p y' h).1 hyP
    have hunit' : IsUnit (ger y' h (p ^ M)) := by
      rw [map_pow]
      exact hunit.pow M
    have e₁ := congrArg (ger y' hyP) e'
    rw [map_mul, ger_resG, ger_resG, ger_resG, hab, map_mul] at e₁
    exact (hunit'.mul_right_cancel e₁).symm
  · have hyP : y' ∉ (Y₀ X Z).basicOpen p := (hbd y' h).1 hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨n, hn⟩ := hb
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    refine hyP (((Y₀ X Z).mem_basicOpen p y' h).2 ?_)
    have h₂ := hu.pow n
    rw [← map_pow, ← hd, map_mul] at h₂
    exact isUnit_of_mul_isUnit_right h₂

end GlobalTheory.CompHS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChartStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

theorem _root_.GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  first | exact @GlobalTheory.CompHS.exists_extension_of_arcZero | exact GlobalTheory.CompHS.exists_extension_of_arcZero | (intros; apply GlobalTheory.CompHS.exists_extension_of_arcZero <;> assumption)
end
end
