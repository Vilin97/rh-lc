module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistenceStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSectionsStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionPlaceValuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNormStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodReductionDvrModelExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopenStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBoundStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSum

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  first | exact @PositivityTheory.Xgn.line_function_place_valuation | exact PositivityTheory.Xgn.line_function_place_valuation
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.line_fn_reads_local_height_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum | exact GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.geometric_component_alg_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | exact GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerChar

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CovEx

theorem exists_padic_emb (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : Nonempty (K →+* ℂ_[p]) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[p]) : K →ₐ[ℚ] ℂ_[p]).toRingHom⟩

theorem goodOf_or {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) : Formalism.L2.Pj.goodOf c σ = σ ∨ (starRingEnd ℂ).comp (Formalism.L2.Pj.goodOf c σ) = σ := by
  unfold Formalism.L2.Pj.goodOf
  split_ifs
  · exact Or.inl rfl
  · right; ext x; simp

theorem exists_constSec : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H),
    ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0,
      s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hR hG E _ _ _ H D l Xo c r U x hL _ χ hχ Z τ
  have hpos := hL.pos
  obtain ⟨κ⟩ := exists_padic_emb c.F (⟨2, Nat.prime_two⟩ : Nat.Primes)
  obtain ⟨O, _, _, _, β, Y, hβ, -, -, -⟩ :=
    GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c ⟨2, Nat.prime_two⟩ κ hpos (hL.good 2 Nat.prime_two)
  obtain ⟨hclopen, hcpt, -⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c (Z : Set (Xo.XF c)) Z.2
  obtain ⟨Z'⟩ := hcpt O β Y hβ
  have hgeom : Z'.IsGeom := GlobalTheory.T.geometric_component_alg_closed E H D l Xo c O β Y Z Z' hβ hL.geo
  obtain ⟨φ, hline, hflat, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 hβ hpos τ.2 hgeom
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 φ hβ hpos τ.2 hgeom hline hflat
  choose t ht ht' using fun σ => hnorm (Formalism.L2.Pj.goodOf c σ)
  have hInf : ∀ σ, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ (t σ) := fun σ => by
    rcases goodOf_or c σ with h | h
    · have := ht σ
      rwa [h] at this
    · have := ht' σ
      rwa [h] at this
  have hFinEx : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ t :=
    fun p κ => GlobalTheory.T.frame_function_finite_norm hR hG E H D l Xo c O β Y Z Z' τ.1 φ p κ hβ hpos τ.2 Z.2 hgeom hflat (hL.good p p.2)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.finite_norm_local_bound E H D l Xo c Z τ.1 φ hFinEx
  obtain ⟨hex, ⟨N, hNinf, hNfin⟩, hdict⟩ := GlobalTheory.T.local_valuation_log_norms_existence c.F (fun σ => Real.exp (t σ)) ρ
  have hinfN : ∀ s, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ s (N.inf s) := fun s => by
    rw [hNinf s, Real.log_exp]
    exact hInf s
  have hfinN : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (N.fin p κ) :=
    fun p κ => by
      obtain ⟨la, π, h1, h2⟩ := hex p κ
      rw [hNfin p κ la π h1 h2]
      exact hρ p κ la π h1 h2
  obtain ⟨hadel, hdeg⟩ := GlobalTheory.T.kronecker_character_frame_bound hR hG E H D l Xo c O β Y _ Z' τ.1 φ N χ hχ hβ hpos τ.2 hclopen hgeom hflat
    hinfN hfinN
  obtain ⟨hsupp, hline'⟩ := hdict N hNinf hNfin
  obtain ⟨s, s', hs, hs', hi, hi', hm, hread⟩ := GlobalTheory.T.flat_on_model_exists_rul_sections E H D l Xo c O β Y Z Z' τ φ hflat
  have hval := GlobalTheory.T.line_fn_reads_local_height_sum E H D l Xo c Z τ s φ ρ hline hread hρ
  have hPts := GlobalTheory.FlatLine.hasPts U hpos hL.good hL.unf Z
  refine ⟨{ sig := s, inv := s', sig_mem := hs, inv_mem := hs', idem_sig := hi, idem_inv := hi', mul_inv := hm,
            cInf := fun σ => Real.exp (t σ), cInf_pos := fun σ => Real.exp_pos _,
            norm_inf := fun σ => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨(hPts.1 σ).1, fun z hz =>
              GlobalTheory.T.unf_section_norm_bound_at_height E H D l Xo c r (Formalism.L2.Pj.goodOf c σ) (U (Formalism.L2.Pj.goodOf c σ)) x Z τ s φ (t σ)
                (Formalism.L2.Pj.goodEmb_goodOf c σ) (hL.unf _ (Formalism.L2.Pj.goodEmb_goodOf c σ))
                (hL.xi _ (Formalism.L2.Pj.goodEmb_goodOf c σ)) hs hline hread (ht σ) z hz ((hPts.1 σ).2 z hz)⟩,
            rho_vw := ρ,
            val_fin := fun w => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨hPts.2 w, fun v hv => by
              simpa using hval w v hv⟩,
            finite_rho := hsupp.1 hadel }, ?_⟩
  exact (hline' hadel).symm.trans hdeg

end GlobalTheory.CompanionTheory.Ar.Br.CovEx
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerCharStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.exists_const_section_kronecker_char : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H), ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0, s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec | exact GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem flatDegreeSt_of_resK_gaga : Geo.ResK.ResKStatement → GagaSections → GlobalTheory.FlatCore.FlatDegreeSt := by
  intro hR hG E _ _ _ H _ _ χ hχ Dw l Xo c r U x hL Z τ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_const_section_kronecker_char hR hG E H Dw l Xo c r U x hL χ hχ Z τ
  let t : GlobalTheory.FlatLine.FlatSec U x Z τ := s.relat (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
    (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
  have ht : t.deg = GlobalTheory.FlatLine.flatDegVal Dw (GlobalTheory.CM.logOm E χ).re := by
    have h2 := GlobalTheory.FlatLine.ConstSec.deg_relat s (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
      (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
    simp only [Pi.zero_apply, zero_sub, neg_mul, finsum_neg_distrib, GlobalTheory.FlatLine.sum_flDefect_vw] at h2
    show (s.relat _ _).deg = _
    rw [h2, hs, GlobalTheory.FlatLine.flatDegVal]; ring
  refine ⟨⟨t⟩, fun s' => ?_⟩
  rw [GlobalTheory.FlatLine.ConstSec.deg_eq hL.unf hL.geo t s', ht, neg_neg]

end GlobalTheory.CompanionTheory.Ar.Br
end
end
end
