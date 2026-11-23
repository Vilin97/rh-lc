module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogShortThetaSeriesDenominatorBoundLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZNonnegAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealIntegralTrivAtPrime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_trivAt_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (ℓ : ℕ), ℓ.Prime → Λ.TrivAt ℓ → ∀ la : HeightOneSpectrum (𝓞 c.F), (ℓ : 𝓞 c.F) ∈ la.asIdeal → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → la.valuation c.F s ≤ 1 := by
  intro E _ _ _ H Dw l c n Λ ℓ hℓ hT la hla s hs
  obtain ⟨k, hk, hkLa, hkstd⟩ := hT
  set w := la.valuation c.F with hwdef
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => hw ⟨x, hx⟩
  have hk1 : w (k : c.F) = 1 := by
    have h := (la.valuation_eq_one_iff_notMem (K := c.F) (r := (k : 𝓞 c.F))).2 ?_
    · simpa using h
    · intro hm
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 c.F) hk)
      have : (1 : 𝓞 c.F) ∈ la.asIdeal := by
        rw [← hab]
        exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hm) (la.asIdeal.mul_mem_left _ hla)
      exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hkv : ∀ τ : E →+* ℂ, w (embF c τ (k : E)) = 1 := fun τ => by rw [map_natCast]; exact hk1
  have hsm : ∀ v : Fin n → Fin n → E,
      (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) • Matrix.of fun i j => v j i := by
    intro v; ext i j; simp [Algebra.smul_def]
  have hdetk : ∀ v : Fin n → Fin n → E,
      Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) ^ n * Matrix.det (Matrix.of fun i j => v j i) := by
    intro v; rw [hsm, Matrix.det_smul, Fintype.card_fin]

  have hei : ∀ i : Fin n, (k : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.Ln := fun i =>
    ⟨hkstd (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_std i)),
      Submodule.smul_mem _ _ (single_std i)⟩
  have hdete : Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • (Pi.single j 1 : Fin n → E)) i) = (k : E) ^ n := by
    rw [hdetk, det_single, _root_.mul_one]
  have hLa : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.La τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, fun i => (hei i).1, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hu : ∀ i, (k : 𝓞 E) • v i ∈ stdLat E n := fun i =>
        hkLa (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hv i))
      obtain ⟨r, hr⟩ := det_std hu
      rw [hdetk] at hr
      have h := hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
      rw [hr] at h
      simp only [map_mul, map_pow, hkv, one_pow, _root_.one_mul] at h
      exact h
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hLn : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.Ln τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, hei, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact (hLa τ).1 _ (Submodule.subset_span ⟨_, ⟨v, fun i => (hv i).1, rfl⟩, rfl⟩)
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hLn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (hLa τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyw⟩ := e1.2
  have := e2.1 y (hs hy)
  simpa [hyw] using this

end GlobalTheory.LatticeIndex
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealIntegralTrivAtPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section


theorem _root_.GlobalTheory.T.intersectedLattice_detIdeal_integral_trivAt_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (ℓ : ℕ), ℓ.Prime → Λ.TrivAt ℓ → ∀ la : HeightOneSpectrum (𝓞 c.F), (ℓ : 𝓞 c.F) ∈ la.asIdeal → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → la.valuation c.F s ≤ 1 := by
  first | exact @GlobalTheory.LatticeIndex.intersected_trivAt_integral | exact GlobalTheory.LatticeIndex.intersected_trivAt_integral | (intros; apply GlobalTheory.LatticeIndex.intersected_trivAt_integral <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShortRuleOfRaw

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.RawSpan

theorem isShortRule_of_raw : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ {n : ℕ} {Λ : GenLat E n} {N : ℕ},
    Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F},
    P ∈ harmL c Λ a → ∀ (x0 : Fin n → Dw.La) (f : Rul Xo c), f ∈ sec Xo c a n →
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (x0Dat c x0) Λ N P y (f p y)) →
    IsShortRule Xo c (GlobalTheory.RawSpan.idCover nab n) Λ N x0 P ((betaH (Dw := Dw) c Λ)⁻¹ • f) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hO a P hP x0 f hf h
  intro k _ _ i1 i2 hk y y₂ hov
  have e : i1 = i2 := (Algebra.algebra_ext _ _ fun a => hk a).symm
  subst e
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  letI : Algebra (idCover nab n).c₂.F k := i1
  have hyy : (y₂ : FrPt Xo c k) = y :=
    GlobalTheory.CoverSec.frOver_unique (idCover nab n) hL.globalFns (frOver_self nab n y₂) hov
  subst hyy
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1
  obtain ⟨p, φ, y0, h0⟩ := hAT k y₂
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) 1
  obtain ⟨v1, hv1, -⟩ := hval k y₂
  have e1 : φ (f p y0) = v1 := hnat p.R k φ y0 y₂ h0 _ _ (h p y0) hv1
  have hsm : (betaH (Dw := Dw) c Λ)⁻¹ • f ∈ sec Xo c a n := Submodule.smul_mem _ _ hf
  have e2 : evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂ = φ (((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0) :=
    GlobalTheory.CoverDescent.evR_of_test hW _ hsm.1 p φ y0 y₂ h0
  have e3 : ((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0 = algebraMap c.F p.R (betaH (Dw := Dw) c Λ)⁻¹ * f p y0 :=
    Algebra.smul_def (betaH (Dw := Dw) c Λ)⁻¹ (f p y0)
  refine ⟨evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂, ?_, ?_⟩
  · have e4 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
    rw [e4, GlobalTheory.LevelCoverDatum.noDelta_w]
    refine (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ (betaH (Dw := Dw) c Λ) hβ N P y₂ _).2 ?_
    rw [e2, e3, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul, e1]
    exact hv1
  · exact ((congrArg (· * evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂) (evR_one_field k y₂)).trans (one_mul _)).symm
end GlobalTheory.RawSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegral

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovInt


set_option maxHeartbeats 1000000 in
theorem integral_smul_thLa : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.log_shortThetaSeriesDenominatorBound_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab
  obtain ⟨hpos, hlog⟩ := hC D T j Y e o Lb a n hH
  refine ⟨intZ D (T.Q.Dw j) Y.d.l₂ n a ^ 2, pow_pos hpos 2, ?_, ?_⟩
  · rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith
  · intro x0 La N P hU hTb hTM hN hP y hval s hs y₁ hy₁
    choose x0' hx0' using fun b => Submodule.Quotient.mk_surjective _ (x0 b)
    have hx : x0 = fun b => (Submodule.Quotient.mk (x0' b) : LevQc (T.Q.Dw j) Y.d.l₂) := funext fun b => (hx0' b).symm
    subst hx
    rw [GlobalTheory.RawSpan.phiHat_indPhi_mk] at hval
    have hsec : (y : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
      have := GlobalTheory.AllWt.cuspW_le_secZ (U := Y.U) (wtZ a n) y.2
      rwa [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat] at this
    have hR := GlobalTheory.RawSpan.isShortRule_of_raw nab hnab hU hTM hN hP x0' _ hsec hval
    obtain ⟨-, hp1, -, hfr, -, -, -, -, -, -, -, -, -, hn8, -, -⟩ := hH
    have hM0 : Y.d.l₂.M ≠ 0 := by
      intro h0
      have hc := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) Y.d.l₂ n
      have hex : Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      rw [h0, zero_pow hex] at hc
      have : intZ D (T.Q.Dw j) Y.d.l₂ n a = 0 := by unfold intZ; rw [hc]; simp
      omega
    have hβ : betaH (Dw := T.Q.Dw j) Y.d.c₂ La ≠ 0 := GlobalTheory.RawSpan.betaH_ne_zero La
    have hg := Submodule.smul_mem _ (betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ hsec
    have hlevI := GlobalTheory.RawSpan.idCover_isLev nab n
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = intZ D (T.Q.Dw j) Y.d.l₂ n a := ⟨_, rfl⟩
    rw [← hZ]
    refine GlobalTheory.AllWt.mem_supLat.2 ?_
    intro la v hv
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul Y.d.c₂.F, hy₁]
    have hV := isVal_valSet la v hv
    have hZ0 : Z ≠ 0 := by rw [hZ]; exact hpos.ne'
    by_cases hb : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ∣ Y.d.l₂.M
    · obtain ⟨ℓ₀, hℓ₀, hm₀, hd₀⟩ := hb
      have hsI := GlobalTheory.T.intersectedLattice_detIdeal_integral_trivAt_prime D.host.E _ (T.Q.Dw j) _ Y.d.c₂ n La ℓ₀ hℓ₀ (GlobalTheory.IntCuspLat.trivAt_of_dvd hTM hd₀) la hm₀ s hs
      rw [smul_comm]
      refine GlobalTheory.IdemInt.nonneg_smul hV hsI ?_
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          ((Z : Y.d.c₂.F)) • ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      have hyZ2 : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          (betaH (Dw := T.Q.Dw j) Y.d.c₂ La * ((Z ^ 2 : ℕ) : Y.d.c₂.F)) •
          ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [smul_smul]
        congr 1
        field_simp
      by_cases h : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ^ 2 ∣ Y.d.l₂.M
      · obtain ⟨ℓ, hℓ, hm, hsq⟩ := h
        have htr : La.TrivAt ℓ := GlobalTheory.IntCuspLat.trivAt_of_dvd hTM
          (dvd_trans (dvd_pow_self ℓ two_ne_zero) hsq)
        rw [hyZ2, hZ]
        exact GlobalTheory.CovInt.SqLev.smul_intZ_sq_nonneg_of_sq_dvd D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la ℓ hℓ hm hsq htr v hv
      · push_neg at h
        rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
        have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
        refine add_nonneg (by exact_mod_cast h1) ?_
        rw [hZ]
        exact GlobalTheory.CovInt.smul_intZ_nonneg_away D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la h v hv
    · push_neg at hb
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (s • (y : Rul Y.d.Xo₂ Y.d.c₂)) =
          ((Z : Y.d.c₂.F)) • ((s * betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
      have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
      refine add_nonneg (by exact_mod_cast h1) ?_
      rw [hZ]
      exact GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
        (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
        la hb s hs v hv

end GlobalTheory.CovInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegralStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  first | exact @GlobalTheory.CovInt.integral_smul_thLa | exact GlobalTheory.CovInt.integral_smul_thLa | (intros; apply GlobalTheory.CovInt.integral_smul_thLa <;> assumption)
end
end
